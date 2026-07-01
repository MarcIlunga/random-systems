/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Applications.XoPANOVA
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Partition.Finpartition

/-!
# XoP Pair-Mayer Scaffold

This file starts XOP-DAG-11.  It names the pair-level Mayer objects that must
be expanded before any colored-bond/rank atomization.  The point is to keep the
pair expansion as the theorem-facing interface and avoid the invalid shortcut
of assigning independent `1 / N` activity to raw colored bonds.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Mayer

open Combinatorics ANOVA

variable {G : Type*} {q : Nat}

/-- Pair index used by the pair-Mayer expansion on a coordinate set. -/
def PairEdge (S : Finset (Fin q)) : Type :=
  { e : (Fin q) × (Fin q) // e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 }

instance pairEdgeFintype (S : Finset (Fin q)) : Fintype (PairEdge S) := by
  unfold PairEdge
  infer_instance

instance pairEdgeDecidableEq (S : Finset (Fin q)) : DecidableEq (PairEdge S) := by
  classical
  infer_instance

/-- The two collision constraints attached to a pair edge. -/
def pairBad [AddGroup G] (y a : Fin q → G) (e : (Fin q) × (Fin q)) : Prop :=
  a e.1 = a e.2 ∨ a e.1 + y e.1 = a e.2 + y e.2

def pairBadHidden (a : Fin q → G) (e : (Fin q) × (Fin q)) : Prop :=
  a e.1 = a e.2

def pairBadShifted [AddGroup G] (y a : Fin q → G) (e : (Fin q) × (Fin q)) : Prop :=
  a e.1 + y e.1 = a e.2 + y e.2

instance pairBad_decidable [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) (e : (Fin q) × (Fin q)) :
    Decidable (pairBad y a e) := by
  unfold pairBad
  infer_instance

instance pairBadHidden_decidable [DecidableEq G]
    (a : Fin q → G) (e : (Fin q) × (Fin q)) :
    Decidable (pairBadHidden a e) := by
  unfold pairBadHidden
  infer_instance

instance pairBadShifted_decidable [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) (e : (Fin q) × (Fin q)) :
    Decidable (pairBadShifted y a e) := by
  unfold pairBadShifted
  infer_instance

/-- Pair-level noncollision predicate. -/
def pairGood [AddGroup G] (y a : Fin q → G) (e : (Fin q) × (Fin q)) : Prop :=
  ¬ pairBad y a e

instance pairGood_decidable [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) (e : (Fin q) × (Fin q)) :
    Decidable (pairGood y a e) := by
  unfold pairGood
  infer_instance

/-- Pair-Mayer edge factor.  The later Penrose/tree-graph proof must work at
this pair-potential level before decomposing the disjunction into colored
constraint atoms. -/
def pairMayerFactor [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) (e : (Fin q) × (Fin q)) : ℝ :=
  if pairBad y a e then -1 else 0

/-- A pair-Mayer factor is pointwise bounded by one in absolute value. -/
theorem abs_pairMayerFactor_le_one [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) (e : (Fin q) × (Fin q)) :
    |pairMayerFactor y a e| ≤ (1 : ℝ) := by
  by_cases h : pairBad y a e
  · simp [pairMayerFactor, h]
  · simp [pairMayerFactor, h]

/-- Atomization of a pair-level Mayer factor.

This lemma is intentionally downstream of the pair-potential definition: it is
the sanctioned bridge to colored hidden/shifted atoms after the pair-Mayer
expansion has been established. -/
theorem pairMayerFactor_atomized [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) (e : (Fin q) × (Fin q)) :
    pairMayerFactor y a e =
      -(if pairBadHidden a e then (1 : ℝ) else 0) -
        (if pairBadShifted y a e then (1 : ℝ) else 0) +
        (if pairBadHidden a e ∧ pairBadShifted y a e then (1 : ℝ) else 0) := by
  by_cases h0 : pairBadHidden a e
  · by_cases h1 : pairBadShifted y a e
    · have h0' : a e.1 = a e.2 := by simpa [pairBadHidden] using h0
      have h1' : a e.1 + y e.1 = a e.2 + y e.2 := by simpa [pairBadShifted] using h1
      simp [pairMayerFactor, pairBad, h0, h1, h0']
    · have h0' : a e.1 = a e.2 := by simpa [pairBadHidden] using h0
      have h1' : ¬ a e.1 + y e.1 = a e.2 + y e.2 := by simpa [pairBadShifted] using h1
      simp [pairMayerFactor, pairBad, h0, h1, h0']
  · by_cases h1 : pairBadShifted y a e
    · have h0' : ¬ a e.1 = a e.2 := by simpa [pairBadHidden] using h0
      have h1' : a e.1 + y e.1 = a e.2 + y e.2 := by simpa [pairBadShifted] using h1
      simp [pairMayerFactor, pairBad, h0, h1, h0', h1']
    · have h0' : ¬ a e.1 = a e.2 := by simpa [pairBadHidden] using h0
      have h1' : ¬ a e.1 + y e.1 = a e.2 + y e.2 := by simpa [pairBadShifted] using h1
      simp [pairMayerFactor, pairBad, h0, h1, h0', h1']

/-- Pair goodness on every coordinate pair is exactly the existing XoP
compatibility predicate. -/
theorem pairGood_coordinates_iff_compatibleHiddenState [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) :
    (∀ e : PairEdge (coordinates q), pairGood y a e.1) ↔
      CompatibleHiddenState y a := by
  constructor
  · intro h
    constructor
    · intro i j haij
      by_cases hij : i = j
      · exact hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hgood : pairGood y a (i, j) :=
          h ⟨(i, j), by simp [coordinates, hijlt]⟩
        exact (hgood (Or.inl haij)).elim
      · have hgood : pairGood y a (j, i) :=
          h ⟨(j, i), by simp [coordinates, hjilt]⟩
        exact (hgood (Or.inl haij.symm)).elim
    · intro i j hshiftij
      by_cases hij : i = j
      · exact hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hgood : pairGood y a (i, j) :=
          h ⟨(i, j), by simp [coordinates, hijlt]⟩
        exact (hgood (Or.inr hshiftij)).elim
      · have hgood : pairGood y a (j, i) :=
          h ⟨(j, i), by simp [coordinates, hjilt]⟩
        exact (hgood (Or.inr hshiftij.symm)).elim
  · intro h e
    rcases h with ⟨ha, hshift⟩
    intro hbad
    rcases e with ⟨⟨i, j⟩, _hi, _hj, hijlt⟩
    have hij : i ≠ j := ne_of_lt hijlt
    rcases hbad with hbad | hbad
    · exact hij (ha hbad)
    · exact hij (hshift hbad)

/-- The finite product of pair-Mayer factors is the indicator that all pair
constraints are good. -/
theorem pairMayer_product_eq_indicator [AddGroup G] [DecidableEq G]
    (S : Finset (Fin q)) (y a : Fin q → G) :
    (∏ e : PairEdge S, (1 + pairMayerFactor y a e.1)) =
      if (∀ e : PairEdge S, pairGood y a e.1) then 1 else 0 := by
  classical
  by_cases h : ∀ e : PairEdge S, pairGood y a e.1
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro e _he
    have hnot : ¬ pairBad y a e.1 := h e
    simp [pairMayerFactor, hnot]
  · rw [if_neg h]
    rcases not_forall.mp h with ⟨e, hegood⟩
    have he : pairBad y a e.1 := by
      simpa [pairGood] using hegood
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by
      simp [pairMayerFactor, he])

/-- Finite Mayer expansion of the pair product over edge families. -/
theorem pairMayer_product_expand [AddGroup G] [DecidableEq G]
    (S : Finset (Fin q)) (y a : Fin q → G) :
    (∏ e : PairEdge S, (1 + pairMayerFactor y a e.1)) =
      ∑ Γ ∈ (Finset.univ : Finset (PairEdge S)).powerset,
        ∏ e ∈ Γ, pairMayerFactor y a e.1 := by
  classical
  simpa using
    (Finset.prod_one_add (s := (Finset.univ : Finset (PairEdge S)))
      (f := fun e => pairMayerFactor y a e.1))

/-- Pair-Mayer hidden partition function over a coordinate set, still before
connected-cluster or colored-atom decomposition. -/
def pairPartition [AddGroup G] [Fintype G] [DecidableEq G]
    (S : Finset (Fin q)) (y : Fin q → G) : ℝ :=
  ∑ a : Fin q → G,
    ∑ Γ ∈ (Finset.univ : Finset (PairEdge S)).powerset,
      ∏ e ∈ Γ, pairMayerFactor y a e.1

/-- Contribution of a fixed pair-edge family before connected-cluster
resummation. -/
def pairFamilyTerm [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) : ℝ :=
  ∑ a : Fin q → G, ∏ e ∈ Γ, pairMayerFactor y a e.1

/-- The pair partition is the sum over all pair-edge families. -/
theorem pairPartition_eq_sum_pairFamilyTerm [AddGroup G] [Fintype G]
    [DecidableEq G] (S : Finset (Fin q)) (y : Fin q → G) :
    pairPartition (G := G) (q := q) S y =
      ∑ Γ ∈ (Finset.univ : Finset (PairEdge S)).powerset,
        pairFamilyTerm (G := G) Γ y := by
  unfold pairPartition pairFamilyTerm
  rw [Finset.sum_comm]

/-- Normalized contribution of a fixed pair-edge family. -/
def normalizedPairFamilyTerm [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) : ℝ :=
  pairFamilyTerm (G := G) Γ y / (visibleNormalizerNNReal (G := G) (q := q) : ℝ)

instance compatibleHiddenState_decidable [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) : Decidable (CompatibleHiddenState y a) :=
  Classical.propDecidable _

/-- Compatible hidden-state count as a real-valued indicator sum. -/
theorem compatibleCountNNReal_eq_sum_indicator [AddGroup G] [Fintype G]
    [DecidableEq G] (y : Fin q → G) :
    ((compatibleCountNNReal y : NNReal) : ℝ) =
      ∑ a : Fin q → G, if CompatibleHiddenState y a then (1 : ℝ) else 0 := by
  rw [compatibleCountNNReal_eq_coe_nat]
  unfold compatibleCountNat
  rw [← Finset.sum_boole (p := fun a : Fin q → G => CompatibleHiddenState y a)
    (s := Finset.univ)]
  simp

/-- On the full coordinate set, the pair-Mayer partition is the existing
compatible hidden-state count. -/
theorem pairPartition_coordinates_eq_compatibleCountNNReal [AddGroup G] [Fintype G]
    [DecidableEq G] (y : Fin q → G) :
    pairPartition (G := G) (q := q) (coordinates q) y =
      ((compatibleCountNNReal y : NNReal) : ℝ) := by
  rw [compatibleCountNNReal_eq_sum_indicator]
  unfold pairPartition
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← pairMayer_product_expand]
  rw [pairMayer_product_eq_indicator]
  by_cases hcomp : CompatibleHiddenState y a
  · rw [if_pos hcomp, if_pos ((pairGood_coordinates_iff_compatibleHiddenState y a).mpr hcomp)]
  · rw [if_neg hcomp]
    exact if_neg (fun hall =>
      hcomp ((pairGood_coordinates_iff_compatibleHiddenState y a).mp hall))

/-- The pair-Mayer partition is exactly the visible density-ratio numerator. -/
theorem visibleDensityRatioReal_eq_pairPartition [AddGroup G] [Fintype G]
    [DecidableEq G] (y : Fin q → G) :
    visibleDensityRatioReal y =
      pairPartition (G := G) (q := q) (coordinates q) y /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  rw [visibleDensityRatioReal_eq]
  rw [pairPartition_coordinates_eq_compatibleCountNNReal]
  simp

/-- The visible density error as a normalized all-edge-family Mayer sum. -/
theorem xopError_eq_normalized_pairFamily_sum_sub_one [AddGroup G] [Fintype G]
    [DecidableEq G] (y : Fin q → G) :
    xopError (G := G) (q := q) y =
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        normalizedPairFamilyTerm (G := G) Γ y) - 1 := by
  unfold xopError visibleDensityErrorReal
  rw [visibleDensityRatioReal_eq_pairPartition]
  rw [pairPartition_eq_sum_pairFamilyTerm]
  simp [normalizedPairFamilyTerm, div_eq_mul_inv, Finset.sum_mul]

/-- The ANOVA component can now be viewed as acting on the all-edge-family
Mayer expansion of the visible density error. -/
theorem anovaComponent_xopError_eq_normalized_pairFamily_sum_sub_one [AddGroup G]
    [Fintype G] [DecidableEq G] (S : Finset (Fin q)) :
    anovaComponent S (xopError (G := G) (q := q)) =
      anovaComponent S (fun y =>
        (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
          normalizedPairFamilyTerm (G := G) Γ y) - 1) := by
  have hf : xopError (G := G) (q := q) = fun y =>
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        normalizedPairFamilyTerm (G := G) Γ y) - 1 := by
    funext y
    exact xopError_eq_normalized_pairFamily_sum_sub_one (G := G) (q := q) y
  rw [hf]

/-- For nonempty supports, the constant `-1` in `R - 1` has zero ANOVA
component, so only the normalized pair-family sum remains. -/
theorem anovaComponent_xopError_eq_normalized_pairFamily_sum_of_nonempty [AddGroup G]
    [Fintype G] [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (hS : S.Nonempty) :
    anovaComponent S (xopError (G := G) (q := q)) =
      anovaComponent S (fun y =>
        ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
          normalizedPairFamilyTerm (G := G) Γ y) := by
  rw [anovaComponent_xopError_eq_normalized_pairFamily_sum_sub_one]
  exact anovaComponent_sub_const_of_nonempty hS _ 1

/-- For nonempty supports, the XoP ANOVA component is the finite sum of the
ANOVA components of individual normalized edge-family terms. -/
theorem anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty [AddGroup G]
    [Fintype G] [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (hS : S.Nonempty) :
    anovaComponent S (xopError (G := G) (q := q)) =
      fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (normalizedPairFamilyTerm (G := G) Γ) y := by
  rw [anovaComponent_xopError_eq_normalized_pairFamily_sum_of_nonempty hS]
  exact anovaComponent_finset_sum S
    ((Finset.univ : Finset (PairEdge (coordinates q))).powerset)
    (fun Γ => normalizedPairFamilyTerm (G := G) Γ)

/-- A pair-Mayer factor only depends on the visible values at its endpoints. -/
theorem pairMayerFactor_eq_of_eq_on_edge [AddGroup G] [DecidableEq G]
    (a y y' : Fin q → G) (e : (Fin q) × (Fin q))
    (h₁ : y e.1 = y' e.1) (h₂ : y e.2 = y' e.2) :
    pairMayerFactor y a e = pairMayerFactor y' a e := by
  simp [pairMayerFactor, pairBad, h₁, h₂]

/-- A pair-Mayer factor only depends on the hidden values at its endpoints. -/
theorem pairMayerFactor_eq_of_eq_on_hidden_edge [AddGroup G] [DecidableEq G]
    (y a a' : Fin q → G) (e : (Fin q) × (Fin q))
    (h₁ : a e.1 = a' e.1) (h₂ : a e.2 = a' e.2) :
    pairMayerFactor y a e = pairMayerFactor y a' e := by
  simp [pairMayerFactor, pairBad, h₁, h₂]

/-- Extend an assignment on a coordinate support to a full tuple.  Values
outside the support are arbitrary and are only used through support-dependence
lemmas. -/
def extendOn [Nonempty G] (U : Finset (Fin q)) (aU : { i : Fin q // i ∈ U } → G) :
    Fin q → G :=
  fun i => if h : i ∈ U then aU ⟨i, h⟩ else Classical.choice inferInstance

theorem extendOn_eq [Nonempty G] (U : Finset (Fin q))
    (aU : { i : Fin q // i ∈ U } → G) {i : Fin q} (hi : i ∈ U) :
    extendOn U aU i = aU ⟨i, hi⟩ := by
  simp [extendOn, hi]

@[simp]
theorem restrictTuple_extendOn [Nonempty G] (U : Finset (Fin q))
    (aU : { i : Fin q // i ∈ U } → G) :
    restrictTuple U (extendOn U aU) = aU := by
  funext i
  exact extendOn_eq U aU i.2

/-- Visible `L¹` average restricted to a coordinate support.  The full tuple
outside the support is filled by `extendOn`; support-invariant functions have
the same full visible `L¹` norm and support-restricted visible `L¹` norm. -/
def visibleL1On [Fintype G] [Nonempty G] (U : Finset (Fin q))
    (f : (Fin q → G) → ℝ) : ℝ :=
  uniformAverage ({ i : Fin q // i ∈ U } → G) (fun aU => |f (extendOn U aU)|)

/-- Uniform averages factor over finite product spaces. -/
theorem uniformAverage_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (f : ∀ i, α i → ℝ) :
    uniformAverage ((i : ι) → α i) (fun a => ∏ i, f i (a i)) =
      ∏ i, uniformAverage (α i) (f i) := by
  classical
  unfold uniformAverage
  have hsum :
      (∑ a : (i : ι) → α i, ∏ i, f i (a i)) =
        ∏ i, ∑ x : α i, f i x := by
    exact (Fintype.prod_sum f).symm
  have hcard :
      (Fintype.card ((i : ι) → α i) : ℝ) =
        ∏ i, (Fintype.card (α i) : ℝ) := by
    exact_mod_cast (Fintype.card_pi : Fintype.card ((i : ι) → α i) =
      ∏ i, Fintype.card (α i))
  rw [hsum, hcard]
  simp_rw [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  simp

/-- Uniform averages are invariant under reindexing by an equivalence. -/
theorem uniformAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    uniformAverage α (fun a => f (e a)) = uniformAverage β f := by
  unfold uniformAverage
  have hsum : (∑ a : α, f (e a)) = ∑ b : β, f b := by
    exact Equiv.sum_comp e f
  have hcard : (Fintype.card α : ℝ) = (Fintype.card β : ℝ) := by
    exact_mod_cast (Fintype.card_congr e)
  rw [hsum, hcard]

/-- Vertices touched by a finite family of pair edges. -/
def edgeVertices {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) : Finset (Fin q) :=
  Γ.biUnion (fun e => {e.1.1, e.1.2})

@[simp]
theorem edgeVertices_empty {S : Finset (Fin q)} :
    edgeVertices (S := S) (∅ : Finset (PairEdge S)) = ∅ := by
  simp [edgeVertices]

theorem edge_left_mem_edgeVertices {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {e : PairEdge S} (he : e ∈ Γ) : e.1.1 ∈ edgeVertices Γ := by
  rw [edgeVertices]
  exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩

theorem edge_right_mem_edgeVertices {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {e : PairEdge S} (he : e ∈ Γ) : e.1.2 ∈ edgeVertices Γ := by
  rw [edgeVertices]
  exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩

theorem edgeVertices_card_ge_two_of_mem {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {e : PairEdge S} (he : e ∈ Γ) : 2 ≤ (edgeVertices Γ).card := by
  have hsubset : ({e.1.1, e.1.2} : Finset (Fin q)) ⊆ edgeVertices Γ := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · subst hi
      exact edge_left_mem_edgeVertices he
    · subst hi
      exact edge_right_mem_edgeVertices he
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2.2.2
  have hcard : ({e.1.1, e.1.2} : Finset (Fin q)).card = 2 := by
    simp [hne]
  calc
    2 = ({e.1.1, e.1.2} : Finset (Fin q)).card := hcard.symm
    _ ≤ (edgeVertices Γ).card := Finset.card_le_card hsubset

/-- A two-point support is exactly the touched-vertex set of one pair edge. -/
theorem exists_pairEdge_edgeVertices_singleton_eq_of_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2) :
    ∃ e : PairEdge S, edgeVertices ({e} : Finset (PairEdge S)) = S := by
  classical
  rcases Finset.card_eq_two.mp hcard with ⟨i, j, hij, rfl⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨⟨(i, j), ?_⟩, ?_⟩
    · simp [hij, hlt]
    · simp [edgeVertices]
  · refine ⟨⟨(j, i), ?_⟩, ?_⟩
    · simp [hij, hgt]
    · simp [edgeVertices, Finset.pair_comm]

/-- Canonical finite-type reindexing for a two-point support. -/
noncomputable def cardTwoSupportEquivFin2 {S : Finset (Fin q)}
    (hcard : S.card = 2) : S ≃ Fin 2 :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans hcard)

/-- Restrict an ambient tuple to a two-point support and reindex it by
`Fin 2`. -/
noncomputable def cardTwoRestrictTuple {α : Type*} {S : Finset (Fin q)}
    (hcard : S.card = 2) (y : Fin q → α) : Fin 2 → α :=
  fun i => y ((cardTwoSupportEquivFin2 (q := q) hcard).symm i)

@[simp]
theorem cardTwoRestrictTuple_apply {α : Type*} {S : Finset (Fin q)}
    (hcard : S.card = 2) (y : Fin q → α) (i : Fin 2) :
    cardTwoRestrictTuple (q := q) hcard y i =
      y ((cardTwoSupportEquivFin2 (q := q) hcard).symm i) := by
  rfl

/-- A two-point support carries only one oriented `PairEdge`: the orientation
is forced by the ambient `Fin q` order. -/
theorem pairEdge_eq_of_support_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2) (e f : PairEdge S) : e = f := by
  classical
  rcases e with ⟨⟨a, b⟩, haS, hbS, hab⟩
  rcases f with ⟨⟨c, d⟩, hcS, hdS, hcd⟩
  apply Subtype.ext
  rcases Finset.card_eq_two.mp hcard with ⟨i, j, _hij, hSij⟩
  have ha : a = i ∨ a = j := by
    have : a ∈ ({i, j} : Finset (Fin q)) := by
      simpa [hSij] using haS
    simpa using this
  have hb : b = i ∨ b = j := by
    have : b ∈ ({i, j} : Finset (Fin q)) := by
      simpa [hSij] using hbS
    simpa using this
  have hc : c = i ∨ c = j := by
    have : c ∈ ({i, j} : Finset (Fin q)) := by
      simpa [hSij] using hcS
    simpa using this
  have hd : d = i ∨ d = j := by
    have : d ∈ ({i, j} : Finset (Fin q)) := by
      simpa [hSij] using hdS
    simpa using this
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  all_goals try (exfalso; exact (ne_of_lt hab) rfl)
  all_goals try (exfalso; exact (ne_of_lt hcd) rfl)
  · rfl
  · exfalso
    exact lt_asymm hab hcd
  · exfalso
    exact lt_asymm hcd hab
  · rfl

/-- A pair edge over a two-point support touches the whole support. -/
theorem edgeVertices_singleton_eq_support_of_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2) (e : PairEdge S) :
    edgeVertices ({e} : Finset (PairEdge S)) = S := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp [edgeVertices] at hi
    rcases hi with hi | hi
    · subst hi
      exact e.2.1
    · subst hi
      exact e.2.2.1
  · rw [hcard]
    have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2.2.2
    have hcard_edge : (edgeVertices ({e} : Finset (PairEdge S))).card = 2 := by
      simp [edgeVertices, hne]
    rw [hcard_edge]

/-- A pair-edge-family term depends only on the visible coordinates touched by
that family. -/
theorem pairFamilyTerm_eq_of_eq_on_edgeVertices [AddGroup G] [Fintype G]
    [DecidableEq G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    {y y' : Fin q → G} (h : ∀ i ∈ edgeVertices Γ, y i = y' i) :
    pairFamilyTerm (G := G) Γ y = pairFamilyTerm (G := G) Γ y' := by
  unfold pairFamilyTerm
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.prod_congr rfl
  intro e he
  exact pairMayerFactor_eq_of_eq_on_edge a y y' e.1
    (h e.1.1 (edge_left_mem_edgeVertices he))
    (h e.1.2 (edge_right_mem_edgeVertices he))

theorem normalizedPairFamilyTerm_eq_of_eq_on_edgeVertices [AddGroup G] [Fintype G]
    [DecidableEq G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    {y y' : Fin q → G} (h : ∀ i ∈ edgeVertices Γ, y i = y' i) :
    normalizedPairFamilyTerm (G := G) Γ y =
    normalizedPairFamilyTerm (G := G) Γ y' := by
  simp [normalizedPairFamilyTerm, pairFamilyTerm_eq_of_eq_on_edgeVertices Γ h]

/-- A normalized pair-edge family term is measurable with respect to its touched
visible vertices. -/
theorem restrictInvariant_normalizedPairFamilyTerm [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    ANOVA.RestrictInvariant (G := G) (q := q) (edgeVertices Γ)
      (normalizedPairFamilyTerm (G := G) Γ) := by
  intro y y' hyy'
  apply normalizedPairFamilyTerm_eq_of_eq_on_edgeVertices
  intro i hi
  have hcoord := congrFun hyy' ⟨i, hi⟩
  simpa [restrictTuple] using hcoord

/-- Projecting an edge-family term to its touched coordinates leaves it
unchanged. -/
theorem project_edgeVertices_normalizedPairFamilyTerm [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    project (edgeVertices Γ) (normalizedPairFamilyTerm (G := G) Γ) =
      normalizedPairFamilyTerm (G := G) Γ := by
  apply project_eq_self_of_restrict_invariant
  intro y y' hyy'
  apply normalizedPairFamilyTerm_eq_of_eq_on_edgeVertices
  intro i hi
  have hcoord := congrFun hyy' ⟨i, hi⟩
  simpa [restrictTuple] using hcoord

/-- Projecting an edge-family term to any superset of its touched coordinates
also leaves it unchanged. -/
theorem project_superset_normalizedPairFamilyTerm [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    {T : Finset (Fin q)} (hΓT : edgeVertices Γ ⊆ T) :
    project T (normalizedPairFamilyTerm (G := G) Γ) =
      normalizedPairFamilyTerm (G := G) Γ := by
  apply project_eq_self_of_restrict_invariant_of_subset (U := edgeVertices Γ) (T := T) hΓT
  intro y y' hyy'
  apply normalizedPairFamilyTerm_eq_of_eq_on_edgeVertices
  intro i hi
  have hcoord := congrFun hyy' ⟨i, hi⟩
  simpa [restrictTuple] using hcoord

/-- Edge-family ANOVA components vanish when the requested support contains a
coordinate not touched by the edge family. -/
theorem anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset [AddGroup G]
    [Fintype G] [DecidableEq G] [Nonempty G]
    (hproj : ANOVA.ProjectionIrrelevance (G := G) (q := q))
    {S₀ : Finset (Fin q)} (Γ : Finset (PairEdge S₀)) {S : Finset (Fin q)}
    (hnot : ¬ S ⊆ edgeVertices Γ) :
    anovaComponent S (normalizedPairFamilyTerm (G := G) Γ) = fun _ => 0 := by
  exact ANOVA.anovaComponent_eq_zero_of_restrict_invariant_of_not_subset
    (G := G) (q := q) hproj
    (normalizedPairFamilyTerm (G := G) Γ)
    (restrictInvariant_normalizedPairFamilyTerm (G := G) (q := q) Γ)
    hnot

/-- Edge-family off-support vanishing with the product-space projection
irrelevance theorem already discharged. -/
theorem anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S₀ : Finset (Fin q)} (Γ : Finset (PairEdge S₀)) {S : Finset (Fin q)}
    (hnot : ¬ S ⊆ edgeVertices Γ) :
    anovaComponent S (normalizedPairFamilyTerm (G := G) Γ) = fun _ => 0 := by
  exact anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset
    (G := G) (q := q) ANOVA.projectionIrrelevance Γ hnot

/-- The `L¹` contribution of an off-support edge-family component is zero. -/
theorem visibleL1_anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S₀ : Finset (Fin q)} (Γ : Finset (PairEdge S₀)) {S : Finset (Fin q)}
    (hnot : ¬ S ⊆ edgeVertices Γ) :
    visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)) = 0 := by
  rw [anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
    (G := G) (q := q) Γ hnot]
  simp [visibleL1, uniformAverage]

/-- Pair-edge families only touch vertices inside their parent support. -/
theorem edgeVertices_subset {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    edgeVertices Γ ⊆ S := by
  intro i hi
  simp [edgeVertices] at hi
  rcases hi with ⟨e, _heΓ, hi | hi⟩
  · subst hi
    exact e.2.1
  · subst hi
    exact e.2.2.1

/-- Adjacency generated by a family of pair edges. -/
def edgeLinked {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (i j : Fin q) : Prop :=
  ∃ e ∈ Γ, (i = e.1.1 ∧ j = e.1.2) ∨ (i = e.1.2 ∧ j = e.1.1)

theorem edgeLinked_symm {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    {i j : Fin q} : edgeLinked Γ i j → edgeLinked Γ j i := by
  intro h
  rcases h with ⟨e, heΓ, hdir | hdir⟩
  · exact ⟨e, heΓ, Or.inr ⟨hdir.2, hdir.1⟩⟩
  · exact ⟨e, heΓ, Or.inl ⟨hdir.2, hdir.1⟩⟩

/-- Pair-edge adjacency has no loops. -/
theorem edgeLinked_irrefl {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (i : Fin q) : ¬ edgeLinked Γ i i := by
  rintro ⟨e, _heΓ, hdir | hdir⟩
  · exact (ne_of_lt e.2.2.2) (hdir.1.symm.trans hdir.2)
  · exact (ne_of_gt e.2.2.2) (hdir.1.symm.trans hdir.2)

/-- The left endpoint of a linked pair belongs to the touched-vertex set. -/
theorem left_mem_edgeVertices_of_edgeLinked {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {i j : Fin q} (h : edgeLinked Γ i j) :
    i ∈ edgeVertices Γ := by
  rcases h with ⟨e, heΓ, hdir | hdir⟩
  · rcases hdir with ⟨rfl, _⟩
    exact edge_left_mem_edgeVertices heΓ
  · rcases hdir with ⟨rfl, _⟩
    exact edge_right_mem_edgeVertices heΓ

/-- The right endpoint of a linked pair belongs to the touched-vertex set. -/
theorem right_mem_edgeVertices_of_edgeLinked {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {i j : Fin q} (h : edgeLinked Γ i j) :
    j ∈ edgeVertices Γ := by
  exact left_mem_edgeVertices_of_edgeLinked (edgeLinked_symm Γ h)

/-- Connectedness of a pair-edge family on its touched vertices. -/
def PairConnected {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) : Prop :=
  ∀ i ∈ edgeVertices Γ, ∀ j ∈ edgeVertices Γ,
    Relation.ReflTransGen (edgeLinked Γ) i j

/-- A singleton pair-edge family is connected on its two touched vertices. -/
theorem pairConnected_singleton {S : Finset (Fin q)} (e : PairEdge S) :
    PairConnected ({e} : Finset (PairEdge S)) := by
  intro i hi j hj
  simp [edgeVertices] at hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi <;> subst hj
  · rfl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨e, by simp, Or.inl ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨e, by simp, Or.inr ⟨rfl, rfl⟩⟩
  · rfl

/-- The simple graph generated by a pair-edge family on its touched vertices. -/
def pairFamilySupportGraph {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    SimpleGraph { i : Fin q // i ∈ edgeVertices Γ } where
  Adj i j := edgeLinked Γ i.1 j.1
  symm := by
    intro i j h
    exact edgeLinked_symm Γ h
  loopless := by
    exact ⟨fun i h => edgeLinked_irrefl Γ i.1 h⟩

instance pairFamilySupportGraphDecidableRel {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    DecidableRel (pairFamilySupportGraph Γ).Adj := by
  classical
  infer_instance

/-- Ambient edge-linked paths lift to paths in the support graph. -/
theorem edgeLinked_reflTransGen_lift_pairFamilySupportGraph {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {i j : Fin q}
    (hi : i ∈ edgeVertices Γ) (hj : j ∈ edgeVertices Γ)
    (h : Relation.ReflTransGen (edgeLinked Γ) i j) :
    Relation.ReflTransGen (pairFamilySupportGraph Γ).Adj ⟨i, hi⟩ ⟨j, hj⟩ := by
  revert hi hj
  induction h with
  | refl =>
      intro hi hj
      rfl
  | tail hprev hstep ih =>
      intro ha hc
      have hb : _ ∈ edgeVertices Γ := left_mem_edgeVertices_of_edgeLinked hstep
      exact Relation.ReflTransGen.tail (ih ha hb) (show (pairFamilySupportGraph Γ).Adj
        ⟨_, hb⟩ ⟨_, hc⟩ from hstep)

/-- Paths in the support graph project to ambient edge-linked paths. -/
theorem pairFamilySupportGraph_reflTransGen_project {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {i j : { i : Fin q // i ∈ edgeVertices Γ }}
    (h : Relation.ReflTransGen (pairFamilySupportGraph Γ).Adj i j) :
    Relation.ReflTransGen (edgeLinked Γ) i.1 j.1 := by
  induction h with
  | refl => rfl
  | tail hprev hstep ih => exact Relation.ReflTransGen.tail ih hstep

/-- The support graph is preconnected exactly when the pair-edge family is
connected.  The nonempty condition is deliberately separated because Mathlib's
`Connected` includes `Nonempty`, while `PairConnected` is vacuous on empty
families. -/
theorem pairFamilySupportGraph_preconnected_iff_pairConnected {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    (pairFamilySupportGraph Γ).Preconnected ↔ PairConnected Γ := by
  constructor
  · intro hpre i hi j hj
    have hreach := hpre ⟨i, hi⟩ ⟨j, hj⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    exact pairFamilySupportGraph_reflTransGen_project hreach
  · intro hconn i j
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact edgeLinked_reflTransGen_lift_pairFamilySupportGraph i.2 j.2
      (hconn i.1 i.2 j.1 j.2)

/-- The support graph is connected iff the pair-edge family is connected and
has at least one touched vertex. -/
theorem pairFamilySupportGraph_connected_iff_pairConnected_and_nonempty {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    (pairFamilySupportGraph Γ).Connected ↔ PairConnected Γ ∧ (edgeVertices Γ).Nonempty := by
  rw [SimpleGraph.connected_iff, pairFamilySupportGraph_preconnected_iff_pairConnected]
  constructor
  · intro h
    constructor
    · exact h.1
    · rcases h.2 with ⟨v⟩
      exact ⟨v.1, v.2⟩
  · intro h
    constructor
    · exact h.1
    · rcases h.2 with ⟨v, hv⟩
      exact ⟨⟨v, hv⟩⟩

/-- Finite visible support of one connected component of a pair-edge family.
This packages Mathlib's quotient-valued connected components back into the
`Finset (Fin q)` supports used by the Mayer/ANOVA layer. -/
noncomputable def pairFamilyComponentVertices {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) : Finset (Fin q) := by
  classical
  exact ((Finset.univ : Finset { i : Fin q // i ∈ edgeVertices Γ }).filter
      (fun i => (pairFamilySupportGraph Γ).connectedComponentMk i = C)).map
    ⟨Subtype.val, by intro a b h; exact Subtype.ext h⟩

theorem mem_pairFamilyComponentVertices_iff {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (i : Fin q) :
    i ∈ pairFamilyComponentVertices Γ C ↔
      ∃ hi : i ∈ edgeVertices Γ,
        (pairFamilySupportGraph Γ).connectedComponentMk ⟨i, hi⟩ = C := by
  classical
  unfold pairFamilyComponentVertices
  constructor
  · intro h
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at h
    rcases h with ⟨v, hvC, hvi⟩
    subst hvi
    exact ⟨v.2, hvC⟩
  · rintro ⟨hi, hiC⟩
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    exact ⟨⟨i, hi⟩, hiC, rfl⟩

theorem pairFamilyComponentVertices_subset_edgeVertices {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    pairFamilyComponentVertices Γ C ⊆ edgeVertices Γ := by
  intro i hi
  rw [mem_pairFamilyComponentVertices_iff] at hi
  exact hi.choose

theorem pairFamilyComponentVertices_nonempty {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    (pairFamilyComponentVertices Γ C).Nonempty := by
  refine SimpleGraph.ConnectedComponent.ind ?_ C
  intro v
  exact ⟨v.1, by
    rw [mem_pairFamilyComponentVertices_iff]
    exact ⟨v.2, rfl⟩⟩

theorem pairFamilyComponentVertices_component_eq_of_mem {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)}
    {C D : (pairFamilySupportGraph Γ).ConnectedComponent} {i : Fin q}
    (hiC : i ∈ pairFamilyComponentVertices Γ C)
    (hiD : i ∈ pairFamilyComponentVertices Γ D) :
    C = D := by
  rw [mem_pairFamilyComponentVertices_iff] at hiC hiD
  rcases hiC with ⟨hiΓC, hiC⟩
  rcases hiD with ⟨hiΓD, hiD⟩
  have hsameSubtype :
      (⟨i, hiΓC⟩ : { i : Fin q // i ∈ edgeVertices Γ }) = ⟨i, hiΓD⟩ :=
    Subtype.ext rfl
  have hsame :
      (pairFamilySupportGraph Γ).connectedComponentMk ⟨i, hiΓC⟩ =
        (pairFamilySupportGraph Γ).connectedComponentMk ⟨i, hiΓD⟩ :=
    congrArg (pairFamilySupportGraph Γ).connectedComponentMk hsameSubtype
  exact hiC.symm.trans (hsame.trans hiD)

theorem pairFamilyComponentVertices_pairwiseDisjoint {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    (Set.univ : Set (pairFamilySupportGraph Γ).ConnectedComponent).PairwiseDisjoint
      (fun C => pairFamilyComponentVertices Γ C) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro C _hC D _hD hnonempty
  rcases hnonempty with ⟨i, hi⟩
  have hiC : i ∈ pairFamilyComponentVertices Γ C := (Finset.mem_inter.mp hi).1
  have hiD : i ∈ pairFamilyComponentVertices Γ D := (Finset.mem_inter.mp hi).2
  exact pairFamilyComponentVertices_component_eq_of_mem hiC hiD

theorem pairFamilyComponentVertices_biUnion_eq_edgeVertices {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent).biUnion
        (fun C => pairFamilyComponentVertices Γ C)) = edgeVertices Γ := by
  classical
  ext i
  constructor
  · intro hi
    rw [Finset.mem_biUnion] at hi
    rcases hi with ⟨C, _hC, hiC⟩
    exact pairFamilyComponentVertices_subset_edgeVertices Γ C hiC
  · intro hiΓ
    rw [Finset.mem_biUnion]
    exact ⟨(pairFamilySupportGraph Γ).connectedComponentMk ⟨i, hiΓ⟩,
      Finset.mem_univ _,
      by
        rw [mem_pairFamilyComponentVertices_iff]
        exact ⟨hiΓ, rfl⟩⟩

theorem sum_card_pairFamilyComponentVertices {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    (∑ C : (pairFamilySupportGraph Γ).ConnectedComponent,
      (pairFamilyComponentVertices Γ C).card) = (edgeVertices Γ).card := by
  classical
  have hdisj :
      ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent) : Set
          (pairFamilySupportGraph Γ).ConnectedComponent).PairwiseDisjoint
        (fun C => pairFamilyComponentVertices Γ C) := by
    simpa using pairFamilyComponentVertices_pairwiseDisjoint Γ
  have hcard := Finset.card_biUnion hdisj
  rw [pairFamilyComponentVertices_biUnion_eq_edgeVertices Γ] at hcard
  exact hcard.symm

/-- The connected components of a pair-edge family form a `Finpartition` of
the touched vertex set.  This is the bridge from arbitrary edge families to the
support-partition index used by the corrected Penrose/Ursell theorem spine. -/
noncomputable def pairFamilyComponentFinpartition {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) : Finpartition (edgeVertices Γ) := by
  classical
  refine Finpartition.ofExistsUnique
    ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent).image
      (fun C => pairFamilyComponentVertices Γ C)) ?hsub ?huniq ?hempty
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨C, _hC, rfl⟩
    exact pairFamilyComponentVertices_subset_edgeVertices Γ C
  · intro a ha
    have ha' : a ∈
        (Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent).biUnion
          (fun C => pairFamilyComponentVertices Γ C) := by
      simpa [pairFamilyComponentVertices_biUnion_eq_edgeVertices Γ] using ha
    rcases Finset.mem_biUnion.mp ha' with ⟨C, _hC, haC⟩
    refine ⟨pairFamilyComponentVertices Γ C, ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩, haC⟩
    · intro t ht
      rcases ht with ⟨htmem, h_at⟩
      rcases Finset.mem_image.mp htmem with ⟨D, _hD, rfl⟩
      exact congrArg (fun C => pairFamilyComponentVertices Γ C)
        (pairFamilyComponentVertices_component_eq_of_mem (q := q) (Γ := Γ) h_at haC)
  · intro hempty
    rcases Finset.mem_image.mp hempty with ⟨C, _hC, hCempty⟩
    exact (pairFamilyComponentVertices_nonempty Γ C).ne_empty hCempty

/-- Independent hidden assignments on every connected-component support. -/
abbrev PairFamilyComponentAssignments {G : Type*} {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :=
  (C : (pairFamilySupportGraph Γ).ConnectedComponent) →
    { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G

noncomputable instance pairFamilyComponentAssignmentsFintype {G : Type*} [Fintype G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    Fintype (PairFamilyComponentAssignments (G := G) Γ) := by
  classical
  infer_instance

/-- Component assignments are equivalent to one assignment on the union of all
touched vertices.  This is the finite-product decomposition needed before the
hidden-state sum can factor over connected components. -/
def pairFamilyComponentAssignmentsEquivSupport {G : Type*} {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    PairFamilyComponentAssignments (G := G) Γ ≃
      ({ i : Fin q // i ∈ edgeVertices Γ } → G) where
  toFun A := fun i =>
    A ((pairFamilySupportGraph Γ).connectedComponentMk i)
      ⟨i.1, by
        rw [mem_pairFamilyComponentVertices_iff]
        exact ⟨i.2, rfl⟩⟩
  invFun a := fun C i =>
    a ⟨i.1, pairFamilyComponentVertices_subset_edgeVertices Γ C i.2⟩
  left_inv := by
    intro A
    funext C i
    simp only
    have hi := (mem_pairFamilyComponentVertices_iff Γ C i.1).mp i.2
    rcases hi with ⟨hiΓ, hiC⟩
    have hsubtype :
        (⟨i.1, pairFamilyComponentVertices_subset_edgeVertices Γ C i.2⟩ :
          { i : Fin q // i ∈ edgeVertices Γ }) = ⟨i.1, hiΓ⟩ := Subtype.ext rfl
    cases hsubtype
    grind [mem_pairFamilyComponentVertices_iff]
  right_inv := by
    intro a
    funext i
    rfl

/-- The subfamily of pair edges lying in a fixed connected component.  We use
the left endpoint as a selector; the right endpoint lies in the same component
because it is adjacent to the left endpoint. -/
noncomputable def pairFamilyComponentEdgeFamily {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) : Finset (PairEdge S) := by
  classical
  exact Γ.filter fun e => ∃ hleft : e.1.1 ∈ edgeVertices Γ,
    (pairFamilySupportGraph Γ).connectedComponentMk ⟨e.1.1, hleft⟩ = C

theorem mem_pairFamilyComponentEdgeFamily_iff {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (e : PairEdge S) :
    e ∈ pairFamilyComponentEdgeFamily Γ C ↔
      e ∈ Γ ∧ ∃ hleft : e.1.1 ∈ edgeVertices Γ,
        (pairFamilySupportGraph Γ).connectedComponentMk ⟨e.1.1, hleft⟩ = C := by
  classical
  simp [pairFamilyComponentEdgeFamily]

theorem edge_left_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {C : (pairFamilySupportGraph Γ).ConnectedComponent} {e : PairEdge S}
    (he : e ∈ pairFamilyComponentEdgeFamily Γ C) :
    e.1.1 ∈ pairFamilyComponentVertices Γ C := by
  rw [mem_pairFamilyComponentVertices_iff]
  rw [mem_pairFamilyComponentEdgeFamily_iff] at he
  exact he.2

theorem edge_right_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {C : (pairFamilySupportGraph Γ).ConnectedComponent} {e : PairEdge S}
    (he : e ∈ pairFamilyComponentEdgeFamily Γ C) :
    e.1.2 ∈ pairFamilyComponentVertices Γ C := by
  rw [mem_pairFamilyComponentVertices_iff]
  rw [mem_pairFamilyComponentEdgeFamily_iff] at he
  rcases he with ⟨heΓ, hleft, hleftC⟩
  have hright : e.1.2 ∈ edgeVertices Γ := edge_right_mem_edgeVertices heΓ
  refine ⟨hright, ?_⟩
  have hadj : (pairFamilySupportGraph Γ).Adj ⟨e.1.1, hleft⟩ ⟨e.1.2, hright⟩ := by
    exact ⟨e, heΓ, Or.inl ⟨rfl, rfl⟩⟩
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hleftC

theorem edgeVertices_pairFamilyComponentEdgeFamily_subset {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    edgeVertices (pairFamilyComponentEdgeFamily Γ C) ⊆ pairFamilyComponentVertices Γ C := by
  intro i hi
  simp [edgeVertices] at hi
  rcases hi with ⟨e, he, hi | hi⟩
  · subst hi
    exact edge_left_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily he
  · subst hi
    exact edge_right_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily he

theorem pairFamilyComponentVertices_subset_edgeVertices_componentEdgeFamily {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    pairFamilyComponentVertices Γ C ⊆ edgeVertices (pairFamilyComponentEdgeFamily Γ C) := by
  intro i hi
  rw [mem_pairFamilyComponentVertices_iff] at hi
  rcases hi with ⟨hiΓ, hiC⟩
  simp [edgeVertices] at hiΓ
  rcases hiΓ with ⟨e, heΓ, hleft | hright⟩
  · subst hleft
    refine edge_left_mem_edgeVertices ?_
    rw [mem_pairFamilyComponentEdgeFamily_iff]
    exact ⟨heΓ, ⟨edge_left_mem_edgeVertices heΓ, hiC⟩⟩
  · subst hright
    refine edge_right_mem_edgeVertices ?_
    rw [mem_pairFamilyComponentEdgeFamily_iff]
    have hleftmem : e.1.1 ∈ edgeVertices Γ := edge_left_mem_edgeVertices heΓ
    have hrightmem : e.1.2 ∈ edgeVertices Γ := edge_right_mem_edgeVertices heΓ
    have hiC' : (pairFamilySupportGraph Γ).connectedComponentMk ⟨e.1.2, hrightmem⟩ = C := by
      simpa using hiC
    have hadj : (pairFamilySupportGraph Γ).Adj ⟨e.1.1, hleftmem⟩ ⟨e.1.2, hrightmem⟩ := by
      exact ⟨e, heΓ, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨heΓ, ⟨hleftmem,
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hiC'⟩⟩

theorem edgeVertices_pairFamilyComponentEdgeFamily {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    edgeVertices (pairFamilyComponentEdgeFamily Γ C) = pairFamilyComponentVertices Γ C := by
  exact le_antisymm (edgeVertices_pairFamilyComponentEdgeFamily_subset Γ C)
    (pairFamilyComponentVertices_subset_edgeVertices_componentEdgeFamily Γ C)

theorem edgeLinked_pairFamilyComponentEdgeFamily_of_edgeLinked
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {C : (pairFamilySupportGraph Γ).ConnectedComponent} {i j : Fin q}
    (hlink : edgeLinked Γ i j) (hiC : i ∈ pairFamilyComponentVertices Γ C) :
    edgeLinked (pairFamilyComponentEdgeFamily Γ C) i j := by
  rcases hlink with ⟨e, heΓ, hdir | hdir⟩
  · rcases hdir with ⟨rfl, rfl⟩
    refine ⟨e, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rw [mem_pairFamilyComponentEdgeFamily_iff]
    rw [mem_pairFamilyComponentVertices_iff] at hiC
    rcases hiC with ⟨hleft, hleftC⟩
    exact ⟨heΓ, ⟨edge_left_mem_edgeVertices heΓ, by simpa using hleftC⟩⟩
  · rcases hdir with ⟨rfl, rfl⟩
    refine ⟨e, ?_, Or.inr ⟨rfl, rfl⟩⟩
    rw [mem_pairFamilyComponentEdgeFamily_iff]
    rw [mem_pairFamilyComponentVertices_iff] at hiC
    rcases hiC with ⟨hright, hrightC⟩
    have hleft : e.1.1 ∈ edgeVertices Γ := edge_left_mem_edgeVertices heΓ
    have hright' : e.1.2 ∈ edgeVertices Γ := edge_right_mem_edgeVertices heΓ
    have hrightC' : (pairFamilySupportGraph Γ).connectedComponentMk ⟨e.1.2, hright'⟩ = C := by
      simpa using hrightC
    have hadj : (pairFamilySupportGraph Γ).Adj ⟨e.1.1, hleft⟩ ⟨e.1.2, hright'⟩ := by
      exact ⟨e, heΓ, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨heΓ, ⟨hleft,
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hrightC'⟩⟩

theorem componentVertices_mem_of_edgeLinked
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {C : (pairFamilySupportGraph Γ).ConnectedComponent} {i j : Fin q}
    (hlink : edgeLinked Γ i j) (hiC : i ∈ pairFamilyComponentVertices Γ C) :
    j ∈ pairFamilyComponentVertices Γ C := by
  have hlinkComp := edgeLinked_pairFamilyComponentEdgeFamily_of_edgeLinked hlink hiC
  have hj : j ∈ edgeVertices (pairFamilyComponentEdgeFamily Γ C) :=
    right_mem_edgeVertices_of_edgeLinked hlinkComp
  rwa [edgeVertices_pairFamilyComponentEdgeFamily] at hj

theorem edgeLinked_reflTransGen_componentEdgeFamily_of_supportGraph
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {C : (pairFamilySupportGraph Γ).ConnectedComponent}
    {u v : { i : Fin q // i ∈ edgeVertices Γ }}
    (huC : u.1 ∈ pairFamilyComponentVertices Γ C)
    (h : Relation.ReflTransGen (pairFamilySupportGraph Γ).Adj u v) :
    Relation.ReflTransGen (edgeLinked (pairFamilyComponentEdgeFamily Γ C)) u.1 v.1 := by
  exact (Relation.ReflTransGen.head_induction_on
    (motive := fun a _h =>
      a.1 ∈ pairFamilyComponentVertices Γ C →
        Relation.ReflTransGen (edgeLinked (pairFamilyComponentEdgeFamily Γ C)) a.1 v.1)
    h
    (by intro _; rfl)
    (by
      intro a c hstep htail ih haC
      exact Relation.ReflTransGen.head
        (edgeLinked_pairFamilyComponentEdgeFamily_of_edgeLinked hstep haC)
        (ih (componentVertices_mem_of_edgeLinked hstep haC)))) huC

theorem pairFamilyComponentEdgeFamily_pairConnected {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    PairConnected (pairFamilyComponentEdgeFamily Γ C) := by
  intro i hi j hj
  have hiC : i ∈ pairFamilyComponentVertices Γ C := by
    rw [← edgeVertices_pairFamilyComponentEdgeFamily]
    exact hi
  have hjC : j ∈ pairFamilyComponentVertices Γ C := by
    rw [← edgeVertices_pairFamilyComponentEdgeFamily]
    exact hj
  rw [mem_pairFamilyComponentVertices_iff] at hiC hjC
  rcases hiC with ⟨hiΓ, hiComp⟩
  rcases hjC with ⟨hjΓ, hjComp⟩
  have hreach : (pairFamilySupportGraph Γ).Reachable ⟨i, hiΓ⟩ ⟨j, hjΓ⟩ := by
    rw [← SimpleGraph.ConnectedComponent.eq]
    exact hiComp.trans hjComp.symm
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  exact edgeLinked_reflTransGen_componentEdgeFamily_of_supportGraph
    (C := C) (u := ⟨i, hiΓ⟩) (v := ⟨j, hjΓ⟩)
    (by rw [mem_pairFamilyComponentVertices_iff]; exact ⟨hiΓ, hiComp⟩) hreach

/-- Connected pair cluster with exact visible support `S`.  Edges live in the
full coordinate set so this type can be summed when expanding an ANOVA
component on a chosen support. -/
structure PairCluster (S : Finset (Fin q)) where
  edges : Finset (PairEdge (coordinates q))
  connected : PairConnected edges
  support_eq : edgeVertices edges = S

/-- Package a singleton ambient pair-edge family as a cluster on its exact
touched support. -/
def singletonPairCluster (e : PairEdge (coordinates q)) :
    PairCluster (edgeVertices ({e} : Finset (PairEdge (coordinates q)))) where
  edges := {e}
  connected := pairConnected_singleton (q := q) e
  support_eq := rfl

/-- A two-point support is the exact support of a singleton pair cluster. -/
noncomputable def singletonPairClusterOfCardEqTwo {S : Finset (Fin q)}
    (hcard : S.card = 2) : PairCluster (q := q) S := by
  classical
  let eS := Classical.choose
    (exists_pairEdge_edgeVertices_singleton_eq_of_card_eq_two (q := q) hcard)
  have hsupportS :
      edgeVertices ({eS} : Finset (PairEdge S)) = S :=
    Classical.choose_spec
      (exists_pairEdge_edgeVertices_singleton_eq_of_card_eq_two (q := q) hcard)
  let e : PairEdge (coordinates q) :=
    ⟨eS.1, by
      simp [coordinates, eS.2.2.2]⟩
  exact
    { edges := {e}
      connected := pairConnected_singleton (q := q) e
      support_eq := by
        rw [← hsupportS]
        simp [edgeVertices, e] }

/-- Package one connected component of an edge family as a `PairCluster`. -/
noncomputable def pairFamilyComponentCluster
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    PairCluster (pairFamilyComponentVertices Γ C) where
  edges := pairFamilyComponentEdgeFamily Γ C
  connected := pairFamilyComponentEdgeFamily_pairConnected Γ C
  support_eq := edgeVertices_pairFamilyComponentEdgeFamily Γ C

theorem pairFamilyComponentEdgeFamily_subset {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    pairFamilyComponentEdgeFamily Γ C ⊆ Γ := by
  intro e he
  exact (mem_pairFamilyComponentEdgeFamily_iff Γ C e).mp he |>.1

theorem mem_pairFamilyComponentEdgeFamily_self_left {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {e : PairEdge S} (he : e ∈ Γ) :
    e ∈ pairFamilyComponentEdgeFamily Γ
      ((pairFamilySupportGraph Γ).connectedComponentMk
        ⟨e.1.1, edge_left_mem_edgeVertices he⟩) := by
  rw [mem_pairFamilyComponentEdgeFamily_iff]
  exact ⟨he, ⟨edge_left_mem_edgeVertices he, rfl⟩⟩

theorem pairFamilyComponentEdgeFamily_component_eq_of_mem {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)}
    {C D : (pairFamilySupportGraph Γ).ConnectedComponent} {e : PairEdge S}
    (heC : e ∈ pairFamilyComponentEdgeFamily Γ C)
    (heD : e ∈ pairFamilyComponentEdgeFamily Γ D) :
    C = D := by
  rw [mem_pairFamilyComponentEdgeFamily_iff] at heC heD
  rcases heC with ⟨_heΓC, hleftC, hC⟩
  rcases heD with ⟨_heΓD, hleftD, hD⟩
  have hsameSubtype :
      (⟨e.1.1, hleftC⟩ : { i : Fin q // i ∈ edgeVertices Γ }) =
        ⟨e.1.1, hleftD⟩ := Subtype.ext rfl
  have hsame :
      (pairFamilySupportGraph Γ).connectedComponentMk ⟨e.1.1, hleftC⟩ =
        (pairFamilySupportGraph Γ).connectedComponentMk ⟨e.1.1, hleftD⟩ :=
    congrArg (pairFamilySupportGraph Γ).connectedComponentMk hsameSubtype
  exact hC.symm.trans (hsame.trans hD)

theorem pairFamilyComponentEdgeFamily_biUnion_eq {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent).biUnion
        (fun C => pairFamilyComponentEdgeFamily Γ C)) = Γ := by
  classical
  ext e
  constructor
  · intro he
    rw [Finset.mem_biUnion] at he
    rcases he with ⟨C, _hC, heC⟩
    exact pairFamilyComponentEdgeFamily_subset Γ C heC
  · intro heΓ
    rw [Finset.mem_biUnion]
    exact ⟨(pairFamilySupportGraph Γ).connectedComponentMk
        ⟨e.1.1, edge_left_mem_edgeVertices heΓ⟩,
      Finset.mem_univ _,
      mem_pairFamilyComponentEdgeFamily_self_left heΓ⟩

theorem pairFamilyComponentEdgeFamily_pairwiseDisjoint {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    (Set.univ : Set (pairFamilySupportGraph Γ).ConnectedComponent).PairwiseDisjoint
      (fun C => pairFamilyComponentEdgeFamily Γ C) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro C _hC D _hD hnonempty
  rcases hnonempty with ⟨e, he⟩
  have heC : e ∈ pairFamilyComponentEdgeFamily Γ C := (Finset.mem_inter.mp he).1
  have heD : e ∈ pairFamilyComponentEdgeFamily Γ D := (Finset.mem_inter.mp he).2
  exact pairFamilyComponentEdgeFamily_component_eq_of_mem heC heD

theorem sum_card_pairFamilyComponentEdgeFamily {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    (∑ C : (pairFamilySupportGraph Γ).ConnectedComponent,
      (pairFamilyComponentEdgeFamily Γ C).card) = Γ.card := by
  classical
  have hdisj :
      ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent) : Set
          (pairFamilySupportGraph Γ).ConnectedComponent).PairwiseDisjoint
        (fun C => pairFamilyComponentEdgeFamily Γ C) := by
    simpa using pairFamilyComponentEdgeFamily_pairwiseDisjoint Γ
  have hcard := Finset.card_biUnion hdisj
  rw [pairFamilyComponentEdgeFamily_biUnion_eq Γ] at hcard
  exact hcard.symm

theorem prod_pairFamilyComponentEdgeFamily {S : Finset (Fin q)}
    {R : Type*} [CommMonoid R] (Γ : Finset (PairEdge S)) (F : PairEdge S → R) :
    (∏ e ∈ Γ, F e) =
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, F e := by
  classical
  have hdisj :
      ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent) : Set
          (pairFamilySupportGraph Γ).ConnectedComponent).PairwiseDisjoint
        (fun C => pairFamilyComponentEdgeFamily Γ C) := by
    simpa using pairFamilyComponentEdgeFamily_pairwiseDisjoint Γ
  calc
    (∏ e ∈ Γ, F e)
        = ∏ e ∈
            ((Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent).biUnion
              (fun C => pairFamilyComponentEdgeFamily Γ C)), F e := by
            rw [pairFamilyComponentEdgeFamily_biUnion_eq Γ]
    _ = ∏ C ∈ (Finset.univ : Finset (pairFamilySupportGraph Γ).ConnectedComponent),
          ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, F e := by
          rw [Finset.prod_biUnion hdisj]
    _ = ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, F e := by
          rfl

theorem prod_pairMayerFactor_pairFamilyComponentEdgeFamily [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y a : Fin q → G) :
    (∏ e ∈ Γ, pairMayerFactor y a e.1) =
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, pairMayerFactor y a e.1 := by
  exact prod_pairFamilyComponentEdgeFamily Γ (fun e => pairMayerFactor y a e.1)

/-- Component-local pair-Mayer product, evaluated from a hidden assignment on
the component support only. -/
def pairFamilyComponentLocalProduct [AddGroup G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (y : Fin q → G)
    (aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ :=
  ∏ e ∈ pairFamilyComponentEdgeFamily Γ C,
    pairMayerFactor y (extendOn (pairFamilyComponentVertices Γ C) aC) e.1

theorem pairFamilyComponentLocalProduct_restrictTuple [AddGroup G] [DecidableEq G]
    [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (y a : Fin q → G) :
    pairFamilyComponentLocalProduct (G := G) Γ C y
        (restrictTuple (pairFamilyComponentVertices Γ C) a) =
      ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, pairMayerFactor y a e.1 := by
  unfold pairFamilyComponentLocalProduct
  refine Finset.prod_congr rfl ?_
  intro e he
  exact pairMayerFactor_eq_of_eq_on_hidden_edge y
    (extendOn (pairFamilyComponentVertices Γ C)
      (restrictTuple (pairFamilyComponentVertices Γ C) a))
    a e.1
    (by
      rw [extendOn_eq _ _ (edge_left_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily he)]
      rfl)
    (by
      rw [extendOn_eq _ _ (edge_right_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily he)]
      rfl)

theorem pairFamilyTerm_eq_sum_component_products [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) :
    pairFamilyTerm (G := G) Γ y =
      ∑ a : Fin q → G,
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, pairMayerFactor y a e.1 := by
  unfold pairFamilyTerm
  refine Finset.sum_congr rfl ?_
  intro a _ha
  exact prod_pairMayerFactor_pairFamilyComponentEdgeFamily Γ y a

theorem pairFamilyTerm_eq_sum_component_localProducts [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (y : Fin q → G) :
    pairFamilyTerm (G := G) Γ y =
      ∑ a : Fin q → G,
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          pairFamilyComponentLocalProduct (G := G) Γ C y
            (restrictTuple (pairFamilyComponentVertices Γ C) a) := by
  rw [pairFamilyTerm_eq_sum_component_products]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  refine Finset.prod_congr rfl ?_
  intro C _hC
  exact (pairFamilyComponentLocalProduct_restrictTuple (G := G) Γ C y a).symm

theorem normalizedPairFamilyTerm_eq_sum_component_products_div [AddGroup G] [Fintype G]
    [DecidableEq G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) :
    normalizedPairFamilyTerm (G := G) Γ y =
      (∑ a : Fin q → G,
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          ∏ e ∈ pairFamilyComponentEdgeFamily Γ C, pairMayerFactor y a e.1) /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  rw [normalizedPairFamilyTerm, pairFamilyTerm_eq_sum_component_products]

theorem normalizedPairFamilyTerm_eq_sum_component_localProducts_div [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (y : Fin q → G) :
    normalizedPairFamilyTerm (G := G) Γ y =
      (∑ a : Fin q → G,
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          pairFamilyComponentLocalProduct (G := G) Γ C y
            (restrictTuple (pairFamilyComponentVertices Γ C) a)) /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  rw [normalizedPairFamilyTerm, pairFamilyTerm_eq_sum_component_localProducts]

/-- A finite hidden-tuple sum whose summand depends only on coordinates in `U`
splits into a support sum times the number of complement assignments. -/
theorem sum_restrictTuple_eq_card_compl_mul_sum [Fintype G] [DecidableEq G]
    (U : Finset (Fin q)) (F : ({ i : Fin q // i ∈ U } → G) → ℝ) :
    (∑ a : Fin q → G, F (restrictTuple U a)) =
      (Fintype.card ({ i : Fin q // i ∉ U } → G) : ℝ) *
        ∑ aU : { i : Fin q // i ∈ U } → G, F aU := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin q => i ∈ U) (fun _ => G)
  calc
    (∑ a : Fin q → G, F (restrictTuple U a)) =
        ∑ p : (({ i : Fin q // i ∈ U } → G) × ({ i : Fin q // ¬ i ∈ U } → G)),
          F p.1 := by
          exact Fintype.sum_equiv e
            (fun a : Fin q → G => F (restrictTuple U a))
            (fun p : (({ i : Fin q // i ∈ U } → G) ×
                ({ i : Fin q // ¬ i ∈ U } → G)) => F p.1)
            (by intro a; rfl)
    _ = ∑ aU : { i : Fin q // i ∈ U } → G,
          ∑ _aC : { i : Fin q // ¬ i ∈ U } → G, F aU := by
          rw [Fintype.sum_prod_type]
    _ = (Fintype.card ({ i : Fin q // i ∉ U } → G) : ℝ) *
          ∑ aU : { i : Fin q // i ∈ U } → G, F aU := by
          simp [Finset.mul_sum]

/-- A support-invariant function has the same full visible `L¹` average as its
support-restricted visible `L¹` average. -/
theorem visibleL1_eq_visibleL1On_of_restrictInvariant [Fintype G] [DecidableEq G]
    [Nonempty G] (U : Finset (Fin q)) (f : (Fin q → G) → ℝ)
    (hinv : ANOVA.RestrictInvariant (G := G) (q := q) U f) :
    visibleL1 f = visibleL1On (G := G) (q := q) U f := by
  classical
  unfold visibleL1 visibleL1On uniformAverage
  have hsum :
      (∑ y : Fin q → G, |f y|) =
        (Fintype.card ({ i : Fin q // i ∉ U } → G) : ℝ) *
          ∑ aU : { i : Fin q // i ∈ U } → G, |f (extendOn U aU)| := by
    calc
      (∑ y : Fin q → G, |f y|)
          = ∑ y : Fin q → G, |f (extendOn U (restrictTuple U y))| := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            have hres :
                restrictTuple U y =
                  restrictTuple U (extendOn U (restrictTuple U y)) := by
              simp
            rw [hinv hres]
      _ = (Fintype.card ({ i : Fin q // i ∉ U } → G) : ℝ) *
            ∑ aU : { i : Fin q // i ∈ U } → G, |f (extendOn U aU)| := by
            exact sum_restrictTuple_eq_card_compl_mul_sum (G := G) (q := q) U
              (fun aU : { i : Fin q // i ∈ U } → G => |f (extendOn U aU)|)
  have hcard_nat :
      Fintype.card (Fin q → G) =
        Fintype.card ({ i : Fin q // i ∈ U } → G) *
          Fintype.card ({ i : Fin q // i ∉ U } → G) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr
      (Equiv.piEquivPiSubtypeProd (fun i : Fin q => i ∈ U) (fun _ => G))
  have hcard :
      (Fintype.card (Fin q → G) : ℝ) =
        (Fintype.card ({ i : Fin q // i ∈ U } → G) : ℝ) *
          (Fintype.card ({ i : Fin q // i ∉ U } → G) : ℝ) := by
    exact_mod_cast hcard_nat
  have hcardU_ne :
      (Fintype.card ({ i : Fin q // i ∈ U } → G) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card ({ i : Fin q // i ∈ U } → G) ≠ 0)
  have hcardC_ne :
      (Fintype.card ({ i : Fin q // i ∉ U } → G) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card ({ i : Fin q // i ∉ U } → G) ≠ 0)
  rw [hsum, hcard]
  field_simp [hcardU_ne, hcardC_ne]

/-- Once a full hidden tuple has been restricted to independent connected
component supports, the sum over component assignments factors as a finite
product of component sums. -/
theorem sum_componentAssignments_prod_localProduct [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (y : Fin q → G) :
    (∑ A : PairFamilyComponentAssignments (G := G) Γ,
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        pairFamilyComponentLocalProduct (G := G) Γ C y (A C)) =
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
          pairFamilyComponentLocalProduct (G := G) Γ C y aC := by
  classical
  exact (Fintype.prod_sum
    (fun C aC => pairFamilyComponentLocalProduct (G := G) Γ C y aC)).symm

/-- Reindexing the component assignment factorization as a sum over one
assignment on the union of all touched vertices. -/
theorem sum_supportAssignments_prod_localProduct [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (y : Fin q → G) :
    (∑ aU : { i : Fin q // i ∈ edgeVertices Γ } → G,
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        pairFamilyComponentLocalProduct (G := G) Γ C y
          (((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ).symm aU) C)) =
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
          pairFamilyComponentLocalProduct (G := G) Γ C y aC := by
  classical
  rw [← sum_componentAssignments_prod_localProduct (G := G) Γ y]
  exact Equiv.sum_comp (pairFamilyComponentAssignmentsEquivSupport (G := G) Γ).symm
    (fun A => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
      pairFamilyComponentLocalProduct (G := G) Γ C y (A C))

/-- Splitting a full hidden tuple through the union support and then through
connected components recovers the direct restriction to each component. -/
theorem pairFamilyComponentAssignmentsEquivSupport_symm_restrictTuple
    {G : Type*} {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (a : Fin q → G)
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    ((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ).symm
      (restrictTuple (edgeVertices Γ) a) C) =
        restrictTuple (pairFamilyComponentVertices Γ C) a := by
  rfl

/-- Full finite-product/fiber factorization of a pair-Mayer family: the full
hidden-state sum is the number of assignments on untouched vertices times the
product of independent connected-component hidden sums. -/
theorem pairFamilyTerm_eq_complementCard_mul_component_sums [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (y : Fin q → G) :
    pairFamilyTerm (G := G) Γ y =
      (Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
            pairFamilyComponentLocalProduct (G := G) Γ C y aC := by
  classical
  rw [pairFamilyTerm_eq_sum_component_localProducts]
  calc
    (∑ a : Fin q → G,
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          pairFamilyComponentLocalProduct (G := G) Γ C y
            (restrictTuple (pairFamilyComponentVertices Γ C) a)) =
        ∑ a : Fin q → G,
          (fun aU : { i : Fin q // i ∈ edgeVertices Γ } → G =>
            ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
              pairFamilyComponentLocalProduct (G := G) Γ C y
                (((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ).symm aU) C))
            (restrictTuple (edgeVertices Γ) a) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.prod_congr rfl ?_
          intro C _hC
          rw [pairFamilyComponentAssignmentsEquivSupport_symm_restrictTuple]
    _ = (Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
          ∑ aU : { i : Fin q // i ∈ edgeVertices Γ } → G,
            ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
              pairFamilyComponentLocalProduct (G := G) Γ C y
                (((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ).symm aU) C) := by
          exact sum_restrictTuple_eq_card_compl_mul_sum (G := G) (q := q)
            (edgeVertices Γ)
            (fun aU : { i : Fin q // i ∈ edgeVertices Γ } → G =>
              ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
                pairFamilyComponentLocalProduct (G := G) Γ C y
                  (((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ).symm aU) C))
    _ = (Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
          ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
            ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
              pairFamilyComponentLocalProduct (G := G) Γ C y aC := by
          rw [sum_supportAssignments_prod_localProduct]

/-- Normalized component-factorization form of a pair-Mayer family. -/
theorem normalizedPairFamilyTerm_eq_complementCard_mul_component_sums_div
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) :
    normalizedPairFamilyTerm (G := G) Γ y =
      ((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
            pairFamilyComponentLocalProduct (G := G) Γ C y aC) /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  rw [normalizedPairFamilyTerm, pairFamilyTerm_eq_complementCard_mul_component_sums]

/-- Hidden sum local to one connected component of a pair-edge family. -/
def pairFamilyComponentLocalSum [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (y : Fin q → G) : ℝ :=
  ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
    pairFamilyComponentLocalProduct (G := G) Γ C y aC

/-- Full hidden summation over the edge family of one connected component equals
the component-local hidden sum times the number of assignments on untouched
coordinates. -/
theorem pairFamilyTerm_componentEdgeFamily_eq_complementCard_mul_localSum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (y : Fin q → G) :
    pairFamilyTerm (G := G) (pairFamilyComponentEdgeFamily Γ C) y =
      (Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → G) : ℝ) *
        pairFamilyComponentLocalSum (G := G) Γ C y := by
  unfold pairFamilyTerm pairFamilyComponentLocalSum
  calc
    (∑ a : Fin q → G, ∏ e ∈ pairFamilyComponentEdgeFamily Γ C,
        pairMayerFactor y a e.1) =
        ∑ a : Fin q → G,
          pairFamilyComponentLocalProduct (G := G) Γ C y
            (restrictTuple (pairFamilyComponentVertices Γ C) a) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact (pairFamilyComponentLocalProduct_restrictTuple (G := G) Γ C y a).symm
    _ =
      (Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → G) : ℝ) *
        ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
          pairFamilyComponentLocalProduct (G := G) Γ C y aC := by
        exact sum_restrictTuple_eq_card_compl_mul_sum (G := G) (q := q)
          (pairFamilyComponentVertices Γ C)
          (fun aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G =>
            pairFamilyComponentLocalProduct (G := G) Γ C y aC)

/-- A component-local product depends only on the visible coordinates in that
component. -/
theorem pairFamilyComponentLocalProduct_eq_of_eq_on_componentVertices
    [AddGroup G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) {y y' : Fin q → G}
    (h : ∀ i ∈ pairFamilyComponentVertices Γ C, y i = y' i)
    (aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) :
    pairFamilyComponentLocalProduct (G := G) Γ C y aC =
      pairFamilyComponentLocalProduct (G := G) Γ C y' aC := by
  unfold pairFamilyComponentLocalProduct
  refine Finset.prod_congr rfl ?_
  intro e he
  exact pairMayerFactor_eq_of_eq_on_edge
    (extendOn (pairFamilyComponentVertices Γ C) aC) y y' e.1
    (h e.1.1 (edge_left_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily he))
    (h e.1.2 (edge_right_mem_pairFamilyComponentVertices_of_mem_componentEdgeFamily he))

/-- A component-local product is pointwise bounded by one in absolute value.
This is only a crude baseline bound; the final activity estimate must still use
rank/cancellation information. -/
theorem abs_pairFamilyComponentLocalProduct_le_one
    [AddGroup G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (y : Fin q → G)
    (aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) :
    |pairFamilyComponentLocalProduct (G := G) Γ C y aC| ≤ (1 : ℝ) := by
  unfold pairFamilyComponentLocalProduct
  rw [Finset.abs_prod]
  calc
    (∏ x ∈ pairFamilyComponentEdgeFamily Γ C,
        |pairMayerFactor y (extendOn (pairFamilyComponentVertices Γ C) aC) x.1|)
        ≤ ∏ _x ∈ pairFamilyComponentEdgeFamily Γ C, (1 : ℝ) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro x hx
            exact abs_nonneg _
          · intro x hx
            exact abs_pairMayerFactor_le_one y
              (extendOn (pairFamilyComponentVertices Γ C) aC) x.1
    _ = 1 := by simp

/-- Crude pointwise bound on a component-local hidden sum by the number of
hidden assignments on that component. -/
theorem abs_pairFamilyComponentLocalSum_le_card
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (y : Fin q → G) :
    |pairFamilyComponentLocalSum (G := G) Γ C y| ≤
      (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ) := by
  unfold pairFamilyComponentLocalSum
  calc
    |∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
        pairFamilyComponentLocalProduct (G := G) Γ C y aC|
        ≤ ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
            |pairFamilyComponentLocalProduct (G := G) Γ C y aC| := by
          exact Finset.abs_sum_le_sum_abs
            (fun aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G =>
              pairFamilyComponentLocalProduct (G := G) Γ C y aC) Finset.univ
    _ ≤ ∑ _aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
            (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro aC _haC
          exact abs_pairFamilyComponentLocalProduct_le_one (G := G) Γ C y aC
    _ = (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ) := by
          simp

/-- Crude `L¹` bound on one component-local hidden sum by the number of hidden
assignments on that component.  This is only a baseline; the theorem-facing
rank/codimension route must replace this with a defect-sensitive estimate. -/
theorem visibleL1_pairFamilyComponentLocalSum_le_card
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    visibleL1 (pairFamilyComponentLocalSum (G := G) Γ C) ≤
      (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ) := by
  let B := (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ)
  have hpoint : ∀ y : Fin q → G,
      |pairFamilyComponentLocalSum (G := G) Γ C y| ≤ B := by
    intro y
    exact abs_pairFamilyComponentLocalSum_le_card (G := G) Γ C y
  unfold visibleL1 uniformAverage
  change (∑ y : Fin q → G, |pairFamilyComponentLocalSum (G := G) Γ C y|) /
      (Fintype.card (Fin q → G) : ℝ) ≤ B
  have hsum :
      (∑ y : Fin q → G, |pairFamilyComponentLocalSum (G := G) Γ C y|) ≤
        ∑ _y : Fin q → G, B := by
    exact Finset.sum_le_sum (fun y _hy => hpoint y)
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin q → G) : ℝ) := Nat.cast_nonneg _
  refine le_trans (div_le_div_of_nonneg_right hsum hcard_nonneg) ?_
  simp [Finset.sum_const, nsmul_eq_mul]

/-- A component-local hidden sum depends only on the visible coordinates in
that component. -/
theorem pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) {y y' : Fin q → G}
    (h : ∀ i ∈ pairFamilyComponentVertices Γ C, y i = y' i) :
    pairFamilyComponentLocalSum (G := G) Γ C y =
      pairFamilyComponentLocalSum (G := G) Γ C y' := by
  unfold pairFamilyComponentLocalSum
  refine Finset.sum_congr rfl ?_
  intro aC _haC
  exact pairFamilyComponentLocalProduct_eq_of_eq_on_componentVertices
    (G := G) Γ C h aC

/-- Reindexing a full touched-support assignment into component assignments
does not change a component-local sum. -/
theorem pairFamilyComponentLocalSum_extendOn_support_eq_component
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (A : PairFamilyComponentAssignments (G := G) Γ)
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    pairFamilyComponentLocalSum (G := G) Γ C
        (extendOn (edgeVertices Γ)
          ((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ) A)) =
      pairFamilyComponentLocalSum (G := G) Γ C
        (extendOn (pairFamilyComponentVertices Γ C) (A C)) := by
  apply pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices
  intro i hi
  have hiΓ : i ∈ edgeVertices Γ := pairFamilyComponentVertices_subset_edgeVertices Γ C hi
  rw [extendOn_eq (edgeVertices Γ)
    ((pairFamilyComponentAssignmentsEquivSupport (G := G) Γ) A) hiΓ]
  rw [extendOn_eq (pairFamilyComponentVertices Γ C) (A C) hi]
  obtain ⟨hiΓ', hcomp⟩ := (mem_pairFamilyComponentVertices_iff Γ C i).mp hi
  have hcomp' :
      (pairFamilySupportGraph Γ).connectedComponentMk ⟨i, hiΓ⟩ = C := by
    have hsub : (⟨i, hiΓ⟩ : { i : Fin q // i ∈ edgeVertices Γ }) = ⟨i, hiΓ'⟩ :=
      Subtype.ext rfl
    rw [hsub]
    exact hcomp
  change
    A ((pairFamilySupportGraph Γ).connectedComponentMk ⟨i, hiΓ⟩) _ =
      A C ⟨i, hi⟩
  cases hcomp'
  rfl

/-- The support-restricted visible `L¹` average of the product of component
local sums factors over connected components. -/
theorem visibleL1On_edgeVertices_prod_pairFamilyComponentLocalSum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    visibleL1On (G := G) (q := q) (edgeVertices Γ)
        (fun y => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          pairFamilyComponentLocalSum (G := G) Γ C y) =
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        visibleL1On (G := G) (q := q) (pairFamilyComponentVertices Γ C)
          (pairFamilyComponentLocalSum (G := G) Γ C) := by
  classical
  let e := pairFamilyComponentAssignmentsEquivSupport (G := G) Γ
  calc
    visibleL1On (G := G) (q := q) (edgeVertices Γ)
        (fun y => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          pairFamilyComponentLocalSum (G := G) Γ C y)
        =
        uniformAverage (PairFamilyComponentAssignments (G := G) Γ)
          (fun A => |∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
            pairFamilyComponentLocalSum (G := G) Γ C
              (extendOn (edgeVertices Γ) (e A))|) := by
          exact (uniformAverage_equiv e
            (fun aU : { i : Fin q // i ∈ edgeVertices Γ } → G =>
              |(fun y : Fin q → G =>
                  ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
                    pairFamilyComponentLocalSum (G := G) Γ C y)
                (extendOn (edgeVertices Γ) aU)|)).symm
    _ =
        uniformAverage (PairFamilyComponentAssignments (G := G) Γ)
          (fun A => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
            |pairFamilyComponentLocalSum (G := G) Γ C
              (extendOn (pairFamilyComponentVertices Γ C) (A C))|) := by
          unfold uniformAverage
          congr 1
          refine Finset.sum_congr rfl ?_
          intro A _hA
          change |∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
              pairFamilyComponentLocalSum (G := G) Γ C
                (extendOn (edgeVertices Γ) (e A))| =
            ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
              |pairFamilyComponentLocalSum (G := G) Γ C
                (extendOn (pairFamilyComponentVertices Γ C) (A C))|
          rw [Finset.abs_prod]
          refine Finset.prod_congr rfl ?_
          intro C _hC
          rw [pairFamilyComponentLocalSum_extendOn_support_eq_component
            (G := G) Γ A C]
    _ =
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          visibleL1On (G := G) (q := q) (pairFamilyComponentVertices Γ C)
            (pairFamilyComponentLocalSum (G := G) Γ C) := by
          exact uniformAverage_pi_prod
            (fun C (aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) =>
              |pairFamilyComponentLocalSum (G := G) Γ C
                (extendOn (pairFamilyComponentVertices Γ C) aC)|)

/-- Support-invariance form of
`pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices`. -/
theorem restrictInvariant_pairFamilyComponentLocalSum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    ANOVA.RestrictInvariant (G := G) (q := q) (pairFamilyComponentVertices Γ C)
      (pairFamilyComponentLocalSum (G := G) Γ C) := by
  intro y y' hyy'
  apply pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices
  intro i hi
  have hcoord := congrFun hyy' ⟨i, hi⟩
  simpa [restrictTuple] using hcoord

/-- Projecting a component-local sum to that component's vertices leaves it
unchanged. -/
theorem project_pairFamilyComponentVertices_localSum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    project (pairFamilyComponentVertices Γ C)
        (pairFamilyComponentLocalSum (G := G) Γ C) =
      pairFamilyComponentLocalSum (G := G) Γ C := by
  exact project_eq_self_of_restrict_invariant (pairFamilyComponentVertices Γ C)
    (pairFamilyComponentLocalSum (G := G) Γ C)
    (restrictInvariant_pairFamilyComponentLocalSum (G := G) (q := q) Γ C)

/-- The product of component-local sums depends only on the union of component
supports, namely the touched vertices of the pair-edge family. -/
theorem restrictInvariant_prod_pairFamilyComponentLocalSum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    ANOVA.RestrictInvariant (G := G) (q := q) (edgeVertices Γ)
      (fun y => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        pairFamilyComponentLocalSum (G := G) Γ C y) := by
  intro y y' hyy'
  refine Finset.prod_congr rfl ?_
  intro C _hC
  apply pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices
  intro i hi
  have hiΓ : i ∈ edgeVertices Γ := pairFamilyComponentVertices_subset_edgeVertices Γ C hi
  have hcoord := congrFun hyy' ⟨i, hiΓ⟩
  simpa [restrictTuple] using hcoord

/-- Product-space visible `L¹` factorization for component-local sums. -/
theorem visibleL1_prod_pairFamilyComponentLocalSum_eq_prod_visibleL1
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    visibleL1 (fun y => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        pairFamilyComponentLocalSum (G := G) Γ C y) =
      ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        visibleL1 (pairFamilyComponentLocalSum (G := G) Γ C) := by
  rw [visibleL1_eq_visibleL1On_of_restrictInvariant (G := G) (q := q)
    (edgeVertices Γ)
    (fun y => ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
      pairFamilyComponentLocalSum (G := G) Γ C y)
    (restrictInvariant_prod_pairFamilyComponentLocalSum (G := G) (q := q) Γ)]
  rw [visibleL1On_edgeVertices_prod_pairFamilyComponentLocalSum (G := G) (q := q) Γ]
  refine Finset.prod_congr rfl ?_
  intro C _hC
  exact (visibleL1_eq_visibleL1On_of_restrictInvariant (G := G) (q := q)
    (pairFamilyComponentVertices Γ C)
    (pairFamilyComponentLocalSum (G := G) Γ C)
    (restrictInvariant_pairFamilyComponentLocalSum (G := G) (q := q) Γ C)).symm

/-- The connected-component factorized form of a normalized pair-edge family.
This is the exact expression left by the finite-product/fiber factorization
leaf; numerical activity estimates should target this expression rather than
the unfactored hidden-state sum. -/
def componentFactorizedNormalizedPairFamilyTerm [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (y : Fin q → G) : ℝ :=
  ((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
    ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
      ∑ aC : { i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G,
        pairFamilyComponentLocalProduct (G := G) Γ C y aC) /
    (visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Crude pointwise bound for the component-factorized term by raw hidden
assignment cardinalities.  This deliberately does not use rank or cancellation;
it is a baseline showing what the final activity estimate must improve. -/
theorem abs_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) :
    |componentFactorizedNormalizedPairFamilyTerm (G := G) Γ y| ≤
    |((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
          ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
            (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ)) /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ)| := by
  unfold componentFactorizedNormalizedPairFamilyTerm
  rw [abs_div, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Finset.abs_prod, Finset.abs_prod]
  refine Finset.prod_le_prod ?_ ?_
  · intro C hC
    exact abs_nonneg _
  · intro C hC
    have hcard_nonneg :
        0 ≤ (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ) :=
      Nat.cast_nonneg _
    have hbound := abs_pairFamilyComponentLocalSum_le_card (G := G) Γ C y
    simpa [pairFamilyComponentLocalSum, abs_of_nonneg hcard_nonneg] using hbound

/-- Crude `L¹` bound for the component-factorized term.  This is a checked
baseline only; it is too weak to be the final birthday-scale estimate. -/
theorem visibleL1_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    visibleL1 (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) ≤
      |((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
          ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
            (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ)) /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ)| := by
  let B :=
    |((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          (Fintype.card ({ i : Fin q // i ∈ pairFamilyComponentVertices Γ C } → G) : ℝ)) /
      (visibleNormalizerNNReal (G := G) (q := q) : ℝ)|
  have hpoint : ∀ y : Fin q → G,
      |componentFactorizedNormalizedPairFamilyTerm (G := G) Γ y| ≤ B := by
    intro y
    exact abs_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard (G := G) Γ y
  unfold visibleL1 uniformAverage
  change (∑ y : Fin q → G, |componentFactorizedNormalizedPairFamilyTerm (G := G) Γ y|) /
      (Fintype.card (Fin q → G) : ℝ) ≤ B
  have hsum :
      (∑ y : Fin q → G, |componentFactorizedNormalizedPairFamilyTerm (G := G) Γ y|) ≤
        (∑ _y : Fin q → G, B) := by
    exact Finset.sum_le_sum (fun y _hy => hpoint y)
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin q → G) : ℝ) := Nat.cast_nonneg _
  refine le_trans (div_le_div_of_nonneg_right hsum hcard_nonneg) ?_
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Named local-sum form of the component-factorized pair-family term. -/
theorem componentFactorizedNormalizedPairFamilyTerm_eq_localSums [AddGroup G]
    [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) :
    componentFactorizedNormalizedPairFamilyTerm (G := G) Γ y =
      ((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          pairFamilyComponentLocalSum (G := G) Γ C y) /
        (visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  rfl

/-- Exact product-space `L¹` identity for the component-factorized
pair-family term.  This closes the averaging part of the component-product
leaf; the remaining activity work is now only the per-component local-sum
estimate. -/
theorem visibleL1_componentFactorizedNormalizedPairFamilyTerm_eq_const_mul_prod_localL1
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    visibleL1 (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) =
      |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) /
          (visibleNormalizerNNReal (G := G) (q := q) : ℝ)| *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          visibleL1 (pairFamilyComponentLocalSum (G := G) Γ C) := by
  have hfun :
      componentFactorizedNormalizedPairFamilyTerm (G := G) Γ =
        fun y => ((Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) /
          (visibleNormalizerNNReal (G := G) (q := q) : ℝ)) *
            ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
              pairFamilyComponentLocalSum (G := G) Γ C y := by
    funext y
    rw [componentFactorizedNormalizedPairFamilyTerm_eq_localSums (G := G) Γ y]
    ring
  rw [hfun]
  rw [visibleL1_const_mul]
  rw [visibleL1_prod_pairFamilyComponentLocalSum_eq_prod_visibleL1 (G := G) (q := q) Γ]

/-- The named component-factorized term is definitionally equal to the
normalized pair-family term by the existing factorization theorem. -/
theorem normalizedPairFamilyTerm_eq_componentFactorized [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    normalizedPairFamilyTerm (G := G) Γ =
      componentFactorizedNormalizedPairFamilyTerm (G := G) Γ := by
  funext y
  exact normalizedPairFamilyTerm_eq_complementCard_mul_component_sums_div (G := G) Γ y

/-- Generic ANOVA `L¹` control specialized to the component-factorized
pair-family term.  The remaining numerical work is now an `L¹` estimate on the
factorized connected-component product itself. -/
theorem visibleL1_anovaComponent_componentFactorized_le [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {S₀ : Finset (Fin q)}
    (S : Finset (Fin q)) (Γ : Finset (PairEdge S₀)) :
    visibleL1 (anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ)) ≤
      (S.powerset.card : ℝ) *
        visibleL1 (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) := by
  exact RandomSystems.Applications.XoP.ANOVA.visibleL1_anovaComponent_le_card_powerset_mul_visibleL1
    (G := G) (q := q) S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ)

/-- The factorized pair-family term has the same visible support as the
normalized pair-family term. -/
theorem restrictInvariant_componentFactorizedNormalizedPairFamilyTerm
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    ANOVA.RestrictInvariant (G := G) (q := q) (edgeVertices Γ)
      (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) := by
  intro y y' hyy'
  rw [← congrFun (normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ) y]
  rw [← congrFun (normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ) y']
  exact restrictInvariant_normalizedPairFamilyTerm (G := G) (q := q) Γ hyy'

/-- Projecting the factorized pair-family term to its touched coordinates
leaves it unchanged. -/
theorem project_edgeVertices_componentFactorizedNormalizedPairFamilyTerm
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    project (edgeVertices Γ) (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) =
      componentFactorizedNormalizedPairFamilyTerm (G := G) Γ := by
  exact project_eq_self_of_restrict_invariant (edgeVertices Γ)
    (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ)
    (restrictInvariant_componentFactorizedNormalizedPairFamilyTerm (G := G) (q := q) Γ)

/-- The simple graph on a pair cluster's visible support. -/
def pairClusterGraph {S : Finset (Fin q)} (C : PairCluster S) : SimpleGraph S where
  Adj i j := edgeLinked C.edges i.1 j.1
  symm := by
    intro i j h
    exact edgeLinked_symm C.edges h
  loopless := by
    exact ⟨fun i h => edgeLinked_irrefl C.edges i.1 h⟩

/-- Ambient edge-linked paths lift to paths in the subtype graph on a cluster
support. -/
theorem edgeLinked_reflTransGen_lift_pairClusterGraph {S : Finset (Fin q)}
    (C : PairCluster S) {i j : Fin q}
    (hi : i ∈ edgeVertices C.edges) (hj : j ∈ edgeVertices C.edges)
    (h : Relation.ReflTransGen (edgeLinked C.edges) i j) :
    Relation.ReflTransGen (pairClusterGraph C).Adj
      ⟨i, by rw [← C.support_eq]; exact hi⟩
      ⟨j, by rw [← C.support_eq]; exact hj⟩ := by
  revert hi hj
  induction h with
  | refl =>
      intro hi hj
      rfl
  | tail hprev hstep ih =>
      intro ha hc
      have hb : _ ∈ edgeVertices C.edges := left_mem_edgeVertices_of_edgeLinked hstep
      exact Relation.ReflTransGen.tail (ih ha hb) (show (pairClusterGraph C).Adj
        ⟨_, by rw [← C.support_eq]; exact hb⟩
        ⟨_, by rw [← C.support_eq]; exact hc⟩ from hstep)

/-- The graph generated by a pair cluster is connected on a nonempty support. -/
theorem pairClusterGraph_connected {S : Finset (Fin q)} (C : PairCluster S)
    (hS : S.Nonempty) :
    (pairClusterGraph C).Connected := by
  rcases hS with ⟨r, hr⟩
  exact (SimpleGraph.connected_iff (G := pairClusterGraph C)).2
    ⟨(fun i j => by
        rw [SimpleGraph.reachable_iff_reflTransGen]
        have hi : i.1 ∈ edgeVertices C.edges := by
          rw [C.support_eq]
          exact i.2
        have hj : j.1 ∈ edgeVertices C.edges := by
          rw [C.support_eq]
          exact j.2
        exact edgeLinked_reflTransGen_lift_pairClusterGraph C hi hj
          (C.connected i.1 hi j.1 hj)),
      (⟨⟨r, hr⟩⟩ : Nonempty S)⟩

/-- A tree on the current support, used as the output object of a future
Penrose tree-graph inequality. -/
def PairTree (S : Finset (Fin q)) : Type :=
  { T : SimpleGraph S // T.IsTree }

instance pairTreeFintype (S : Finset (Fin q)) : Fintype (PairTree S) := by
  unfold PairTree
  classical
  infer_instance

/-- A tree is contained in a pair cluster if every tree edge is one of the
cluster's pair links. -/
def PairTreeSubcluster {S : Finset (Fin q)} (C : PairCluster S) (T : PairTree S) : Prop :=
  T.1 ≤ pairClusterGraph C

/-- Every pair cluster with nonempty support admits a spanning tree subcluster. -/
theorem exists_pairCluster_spanningTree {S : Finset (Fin q)} (C : PairCluster S)
    (hS : S.Nonempty) :
    ∃ T : PairTree S, PairTreeSubcluster C T := by
  rcases (pairClusterGraph_connected C hS).exists_isTree_le with ⟨T, hTle, hTtree⟩
  exact ⟨⟨T, hTtree⟩, hTle⟩

/-- An arbitrary spanning tree selected from a nonempty pair cluster. -/
noncomputable def pairClusterSpanningTree {S : Finset (Fin q)} (C : PairCluster S)
    (hS : S.Nonempty) : PairTree S :=
  Classical.choose (exists_pairCluster_spanningTree C hS)

/-- The selected spanning tree is a subcluster of the original pair cluster. -/
theorem pairClusterSpanningTree_subcluster {S : Finset (Fin q)} (C : PairCluster S)
    (hS : S.Nonempty) :
    PairTreeSubcluster C (pairClusterSpanningTree C hS) := by
  exact Classical.choose_spec (exists_pairCluster_spanningTree C hS)

instance pairClusterFintype (S : Finset (Fin q)) : Fintype (PairCluster S) := by
  classical
  letI : DecidablePred
      (fun Γ : Finset (PairEdge (coordinates q)) =>
        PairConnected Γ ∧ edgeVertices Γ = S) := Classical.decPred _
  refine Fintype.ofEquiv
    { Γ : Finset (PairEdge (coordinates q)) // PairConnected Γ ∧ edgeVertices Γ = S } ?_
  exact
    { toFun := fun Γ => ⟨Γ.1, Γ.2.1, Γ.2.2⟩
      invFun := fun C => ⟨C.edges, C.connected, C.support_eq⟩
      left_inv := by
        intro Γ
        rfl
      right_inv := by
        intro C
        rfl }

/-- The complete ambient pair-edge family induced by a support `S`.  This is
the canonical fallback cluster used by total support-partition selectors when
the actual edge family does not cover the requested support. -/
def completePairEdgeFamily (S : Finset (Fin q)) : Finset (PairEdge (coordinates q)) :=
  (Finset.univ : Finset (PairEdge (coordinates q))).filter
    (fun e => e.1.1 ∈ S ∧ e.1.2 ∈ S)

theorem edgeVertices_completePairEdgeFamily {S : Finset (Fin q)}
    (hS : 2 ≤ S.card) :
    edgeVertices (completePairEdgeFamily (q := q) S) = S := by
  classical
  ext i
  constructor
  · intro hi
    rw [edgeVertices] at hi
    rcases Finset.mem_biUnion.mp hi with ⟨e, he, hiEdge⟩
    rw [completePairEdgeFamily] at he
    have hends : e.1.1 ∈ S ∧ e.1.2 ∈ S := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiEdge
    rcases hiEdge with hiEdge | hiEdge
    · simpa [hiEdge] using hends.1
    · simpa [hiEdge] using hends.2
  · intro hiS
    have hSone : 1 < S.card := by omega
    rcases Finset.one_lt_card.mp hSone with ⟨a, ha, b, hb, hab⟩
    let j : Fin q := if i = a then b else a
    have hjS : j ∈ S := by
      dsimp [j]
      split_ifs
      · exact hb
      · exact ha
    have hij_ne : i ≠ j := by
      dsimp [j]
      split_ifs with hia
      · subst hia
        exact hab
      · exact hia
    rcases lt_or_gt_of_ne hij_ne with hij | hji
    · let e : PairEdge (coordinates q) :=
        ⟨(i, j), by simp [coordinates, hij]⟩
      have he : e ∈ completePairEdgeFamily (q := q) S := by
        rw [completePairEdgeFamily]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hiS, hjS⟩
      rw [edgeVertices]
      exact Finset.mem_biUnion.mpr ⟨e, he, by simp [e]⟩
    · let e : PairEdge (coordinates q) :=
        ⟨(j, i), by simp [coordinates, hji]⟩
      have he : e ∈ completePairEdgeFamily (q := q) S := by
        rw [completePairEdgeFamily]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hjS, hiS⟩
      rw [edgeVertices]
      exact Finset.mem_biUnion.mpr ⟨e, he, by simp [e]⟩

theorem completePairEdgeFamily_pairConnected {S : Finset (Fin q)}
    (hS : 2 ≤ S.card) :
    PairConnected (completePairEdgeFamily (q := q) S) := by
  classical
  intro i hi j hj
  have hiS : i ∈ S := by
    rwa [edgeVertices_completePairEdgeFamily (q := q) hS] at hi
  have hjS : j ∈ S := by
    rwa [edgeVertices_completePairEdgeFamily (q := q) hS] at hj
  by_cases hij_eq : i = j
  · subst hij_eq
    exact Relation.ReflTransGen.refl
  · rcases lt_or_gt_of_ne hij_eq with hij | hji
    · let e : PairEdge (coordinates q) :=
        ⟨(i, j), by simp [coordinates, hij]⟩
      have he : e ∈ completePairEdgeFamily (q := q) S := by
        rw [completePairEdgeFamily]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hiS, hjS⟩
      exact Relation.ReflTransGen.single
        (by exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    · let e : PairEdge (coordinates q) :=
        ⟨(j, i), by simp [coordinates, hji]⟩
      have he : e ∈ completePairEdgeFamily (q := q) S := by
        rw [completePairEdgeFamily]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hjS, hiS⟩
      exact Relation.ReflTransGen.single
        (by exact ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩)

theorem exists_pairCluster_of_two_le_card {S : Finset (Fin q)}
    (hS : 2 ≤ S.card) :
    Nonempty (PairCluster (q := q) S) := by
  refine ⟨
    { edges := completePairEdgeFamily (q := q) S
      connected := ?_
      support_eq := ?_ }⟩
  · exact completePairEdgeFamily_pairConnected (q := q) hS
  · exact edgeVertices_completePairEdgeFamily (q := q) hS

/-- A pair cluster support is always a subset of the full coordinate set. -/
theorem pairCluster_support_mem_powerset (S : Finset (Fin q)) (C : PairCluster S) :
    S ∈ (coordinates q).powerset := by
  rw [Finset.mem_powerset]
  rw [← C.support_eq]
  exact edgeVertices_subset C.edges

theorem pairCluster_edges_nonempty_of_support_nonempty
    {S : Finset (Fin q)} (C : PairCluster S) (hS : S.Nonempty) :
    C.edges.Nonempty := by
  by_contra hempty
  have hedge : C.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hSempty : S = ∅ := by
    rw [← C.support_eq, hedge]
    simp
  exact Finset.nonempty_iff_ne_empty.mp hS hSempty

/-- View one ambient edge of a pair cluster as an edge over the cluster's exact
support.  `PairCluster` stores edges over `coordinates q`; rank atomization
needs the same edge typed over the block support. -/
def pairClusterSupportEdge {S : Finset (Fin q)} (C : PairCluster S)
    (e : {e : PairEdge (coordinates q) // e ∈ C.edges}) : PairEdge S := by
  refine ⟨e.1.1, ?_, ?_, e.1.2.2.2⟩
  · have hleft : e.1.1.1 ∈ edgeVertices C.edges := edge_left_mem_edgeVertices e.2
    rwa [C.support_eq] at hleft
  · have hright : e.1.1.2 ∈ edgeVertices C.edges := edge_right_mem_edgeVertices e.2
    rwa [C.support_eq] at hright

/-- The edge set of a pair cluster, retyped over its exact support. -/
def pairClusterSupportEdges {S : Finset (Fin q)} (C : PairCluster S) :
    Finset (PairEdge S) :=
  C.edges.attach.image (pairClusterSupportEdge C)

theorem pairClusterSupportEdge_injective {S : Finset (Fin q)} (C : PairCluster S) :
    Function.Injective (pairClusterSupportEdge C) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : PairEdge S => x.1) h

theorem pairClusterSupportEdge_mem_supportEdges {S : Finset (Fin q)}
    (C : PairCluster S) (e : {e : PairEdge (coordinates q) // e ∈ C.edges}) :
    pairClusterSupportEdge C e ∈ pairClusterSupportEdges C := by
  unfold pairClusterSupportEdges
  exact Finset.mem_image.mpr ⟨e, Finset.mem_attach _ _, rfl⟩

@[simp]
theorem card_pairClusterSupportEdges {S : Finset (Fin q)} (C : PairCluster S) :
    (pairClusterSupportEdges C).card = C.edges.card := by
  rw [pairClusterSupportEdges]
  rw [Finset.card_image_of_injective _ (pairClusterSupportEdge_injective C)]
  simp

/-- Retyping a cluster's edges over its support preserves the touched vertices. -/
@[simp]
theorem edgeVertices_pairClusterSupportEdges {S : Finset (Fin q)} (C : PairCluster S) :
    edgeVertices (pairClusterSupportEdges C) = S := by
  ext i
  constructor
  · intro hi
    rw [edgeVertices] at hi
    rcases Finset.mem_biUnion.mp hi with ⟨eS, heS, hiPair⟩
    rw [pairClusterSupportEdges] at heS
    rcases Finset.mem_image.mp heS with ⟨e, _heAttach, rfl⟩
    have he : e.1 ∈ C.edges := e.2
    have hiEdge : i ∈ edgeVertices C.edges := by
      rw [edgeVertices]
      exact Finset.mem_biUnion.mpr ⟨e.1, he, by simpa [pairClusterSupportEdge] using hiPair⟩
    rwa [C.support_eq] at hiEdge
  · intro hiS
    have hiEdge : i ∈ edgeVertices C.edges := by
      rwa [C.support_eq]
    rw [edgeVertices] at hiEdge ⊢
    rcases Finset.mem_biUnion.mp hiEdge with ⟨e, he, hiPair⟩
    refine Finset.mem_biUnion.mpr
      ⟨pairClusterSupportEdge C ⟨e, he⟩,
        pairClusterSupportEdge_mem_supportEdges C ⟨e, he⟩, ?_⟩
    simpa [pairClusterSupportEdge] using hiPair

theorem edgeLinked_pairClusterSupportEdges_of_edgeLinked {S : Finset (Fin q)}
    (C : PairCluster S) {i j : Fin q}
    (h : edgeLinked C.edges i j) :
    edgeLinked (pairClusterSupportEdges C) i j := by
  rcases h with ⟨e, he, hdir⟩
  refine ⟨pairClusterSupportEdge C ⟨e, he⟩,
    pairClusterSupportEdge_mem_supportEdges C ⟨e, he⟩, ?_⟩
  simpa [pairClusterSupportEdge] using hdir

/-- Retyping a cluster's edges over its support preserves connectedness. -/
theorem pairClusterSupportEdges_pairConnected {S : Finset (Fin q)} (C : PairCluster S) :
    PairConnected (pairClusterSupportEdges C) := by
  intro i hi j hj
  have hiEdge : i ∈ edgeVertices C.edges := by
    rw [C.support_eq]
    rwa [edgeVertices_pairClusterSupportEdges] at hi
  have hjEdge : j ∈ edgeVertices C.edges := by
    rw [C.support_eq]
    rwa [edgeVertices_pairClusterSupportEdges] at hj
  exact (C.connected i hiEdge j hjEdge).mono
    (fun _ _ h => edgeLinked_pairClusterSupportEdges_of_edgeLinked C h)

theorem pairClusterSupportEdges_nonempty_of_support_nonempty
    {S : Finset (Fin q)} (C : PairCluster S) (hS : S.Nonempty) :
    (pairClusterSupportEdges C).Nonempty := by
  rcases pairCluster_edges_nonempty_of_support_nonempty C hS with ⟨e, he⟩
  exact ⟨pairClusterSupportEdge C ⟨e, he⟩,
    pairClusterSupportEdge_mem_supportEdges C ⟨e, he⟩⟩

/-- A pair cluster on a two-point support has a singleton support-retyped edge
family. -/
theorem exists_pairClusterSupportEdges_eq_singleton_of_support_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2) (C : PairCluster S) :
    ∃ e : PairEdge S, pairClusterSupportEdges C = {e} := by
  classical
  have hS : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hSempty
    rw [hSempty] at hcard
    simp at hcard
  rcases pairClusterSupportEdges_nonempty_of_support_nonempty C hS with ⟨e, he⟩
  refine ⟨e, ?_⟩
  ext f
  constructor
  · intro hf
    have hfe : f = e := pairEdge_eq_of_support_card_eq_two (q := q) hcard f e
    simp [hfe]
  · intro hf
    have hfe : f = e := Finset.mem_singleton.mp hf
    rw [hfe]
    exact he

theorem pairCluster_support_card_ge_two_of_nonempty
    {S : Finset (Fin q)} (C : PairCluster S) (hS : S.Nonempty) :
    2 ≤ S.card := by
  rcases pairCluster_edges_nonempty_of_support_nonempty C hS with ⟨e, he⟩
  rw [← C.support_eq]
  exact edgeVertices_card_ge_two_of_mem he

/-- There are no pair clusters on a nonempty support of size below two. -/
theorem pairCluster_sum_eq_zero_of_nonempty_card_lt_two
    {S : Finset (Fin q)} {R : Type*} [AddCommMonoid R]
    (hS : S.Nonempty) (hcard : S.card < 2)
    (f : PairCluster S → R) :
    (∑ C : PairCluster S, f C) = 0 := by
  exact Finset.sum_eq_zero (fun C _ =>
    False.elim ((not_le_of_gt hcard) (pairCluster_support_card_ge_two_of_nonempty C hS)))

/-- Raw product contribution of one connected pair cluster.  This is a named
candidate object, not the final Penrose/cumulant contribution required by
`PairClusterExpansion`. -/
def rawClusterContribution [AddGroup G] [Fintype G] [DecidableEq G]
    (S : Finset (Fin q)) (C : PairCluster S) : (Fin q → G) → ℝ :=
  fun y =>
    (∑ a : Fin q → G, ∏ e ∈ C.edges, pairMayerFactor y a e.1) /
      (visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- The raw connected-cluster product contribution is exactly the normalized
pair-family term for the cluster's edge set.  This is only a bridge for later
comparisons; the final Penrose contribution is expected to include further
cumulant cancellation. -/
theorem rawClusterContribution_eq_normalizedPairFamilyTerm
    [AddGroup G] [Fintype G] [DecidableEq G] {S : Finset (Fin q)}
    (C : PairCluster S) :
    rawClusterContribution (G := G) (q := q) S C =
      normalizedPairFamilyTerm (G := G) C.edges := by
  rfl

/-- A family of connected pair-cluster contribution functions. -/
abbrev PairClusterContribution [AddGroup G] [Fintype G] [DecidableEq G] :=
  (S : Finset (Fin q)) → PairCluster S → (Fin q → G) → ℝ

/-- A theorem-facing contribution family indexed by an arbitrary finite type
depending on the ANOVA support.

This is the corrected interface for the genuine cumulant/Penrose expansion of
`R - 1`: after disconnected pair-edge families are regrouped, one ANOVA
component may naturally be a sum over products of several connected
contributions rather than over a single `PairCluster S`. -/
abbrev SupportIndexedContribution [AddGroup G] [Fintype G] [DecidableEq G]
    (Index : Finset (Fin q) → Type*) :=
  (S : Finset (Fin q)) → Index S → (Fin q → G) → ℝ

/-- Support-partition indices for the corrected Penrose/Ursell expansion:
partition the ANOVA support into nonempty blocks, then attach one connected
pair cluster to each block. -/
abbrev SupportPartitionClusters (S : Finset (Fin q)) : Type :=
  Σ P : Finpartition S, (B : P.parts) → PairCluster B.1

/-- A source-faithful block decoration for covering edge families before the
Ursell/Penrose contraction has removed off-support vertices.  The attached
cluster may have support strictly larger than the visible block of `S`; this is
the information that a direct selector into `SupportPartitionClusters S` would
erase. -/
structure SupportPartitionAmbientBlock (B : Finset (Fin q)) where
  support : Finset (Fin q)
  cluster : PairCluster support
  block_subset : B ⊆ support

instance supportPartitionAmbientBlockFintype (B : Finset (Fin q)) :
    Fintype (SupportPartitionAmbientBlock (q := q) B) := by
  classical
  letI : DecidablePred
      (fun x : Σ support : Finset (Fin q), PairCluster (q := q) support =>
        B ⊆ x.1) := Classical.decPred _
  refine Fintype.ofEquiv
    { x : Σ support : Finset (Fin q), PairCluster (q := q) support // B ⊆ x.1 } ?_
  exact
    { toFun := fun x =>
        { support := x.1.1
          cluster := x.1.2
          block_subset := x.2 }
      invFun := fun A => ⟨⟨A.support, A.cluster⟩, A.block_subset⟩
      left_inv := by
        intro x
        cases x with
        | mk val h =>
          cases val
          rfl
      right_inv := by
        intro A
        cases A
        rfl }

noncomputable instance supportPartitionAmbientBlockDecidableEq (B : Finset (Fin q)) :
    DecidableEq (SupportPartitionAmbientBlock (q := q) B) := by
  classical
  exact Classical.decEq _

/-- Support partitions whose blocks carry ambient connected clusters.  This is
the source-faithful intermediate index for the covering-family selector branch:
partition the ANOVA support `S`, but keep the actual ambient component support
attached to each block until a separate Ursell/Penrose contraction discharges
the off-support vertices. -/
abbrev SupportPartitionAmbientClusters (S : Finset (Fin q)) : Type :=
  Σ P : Finpartition S, (B : P.parts) → SupportPartitionAmbientBlock (q := q) B.1

instance supportPartitionAmbientClustersFintype (S : Finset (Fin q)) :
    Fintype (SupportPartitionAmbientClusters (q := q) S) := by
  classical
  unfold SupportPartitionAmbientClusters
  infer_instance

instance supportPartitionAmbientClustersDecidableEq (S : Finset (Fin q)) :
    DecidableEq (SupportPartitionAmbientClusters (q := q) S) := by
  classical
  unfold SupportPartitionAmbientClusters
  infer_instance

instance supportPartitionAmbientClustersFintypeFamily :
    (S : Finset (Fin q)) → Fintype (SupportPartitionAmbientClusters (q := q) S) :=
  fun S => supportPartitionAmbientClustersFintype (q := q) S

instance supportPartitionAmbientClustersDecidableEqFamily :
    (S : Finset (Fin q)) → DecidableEq (SupportPartitionAmbientClusters (q := q) S) :=
  fun S => supportPartitionAmbientClustersDecidableEq (q := q) S

/-- Support-partition indices carrying only selected trees on each block.  This
is the tree-charge analogue of `SupportPartitionClusters`; the actual
Penrose/Ursell contribution may use it after the connected cluster expansion is
collapsed to tree fibers. -/
abbrev SupportPartitionTrees (S : Finset (Fin q)) : Type :=
  Σ P : Finpartition S, (B : P.parts) → PairTree B.1

/-- The connected cluster associated with one block of the component
finpartition of an edge family. -/
noncomputable def pairFamilyComponentClusterOfPart
    (Γ : Finset (PairEdge (coordinates q))) (B : (pairFamilyComponentFinpartition Γ).parts) :
    PairCluster B.1 := by
  classical
  have hB := B.2
  dsimp [pairFamilyComponentFinpartition] at hB
  let C : (pairFamilySupportGraph Γ).ConnectedComponent := Classical.choose (Finset.mem_image.mp hB)
  have hCeq : pairFamilyComponentVertices Γ C = B.1 :=
    (Classical.choose_spec (Finset.mem_image.mp hB)).2
  exact
    { edges := pairFamilyComponentEdgeFamily Γ C
      connected := pairFamilyComponentEdgeFamily_pairConnected Γ C
      support_eq := (edgeVertices_pairFamilyComponentEdgeFamily Γ C).trans hCeq }

theorem pairFamilyComponentClusterOfPart_edges_subset
    (Γ : Finset (PairEdge (coordinates q)))
    (B : (pairFamilyComponentFinpartition Γ).parts) :
    (pairFamilyComponentClusterOfPart (q := q) Γ B).edges ⊆ Γ := by
  classical
  unfold pairFamilyComponentClusterOfPart
  exact pairFamilyComponentEdgeFamily_subset Γ
    (Classical.choose (Finset.mem_image.mp B.2))

/-- A harmless ambient support-partition index used when a total selector is
queried on a non-covering edge family.  The selector specification is only
claimed on covering families, but the function itself must be total. -/
noncomputable def supportPartitionAmbientFallback (S : Finset (Fin q))
    (hS : S.Nonempty) (hge : 2 ≤ S.card) :
    SupportPartitionAmbientClusters (q := q) S :=
  ⟨Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.mp hS),
    fun B =>
      { support := S
        cluster := Classical.choice (exists_pairCluster_of_two_le_card (q := q) hge)
        block_subset := Finpartition.subset
          (P := Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.mp hS)) B.2 }⟩

/-- A part of the restricted component partition comes from a unique ambient
component part before intersecting with `S`. -/
theorem exists_component_part_of_mem_restrict
    (Γ : Finset (PairEdge (coordinates q))) {S : Finset (Fin q)}
    (hcover : S ⊆ edgeVertices Γ)
    (B : ((pairFamilyComponentFinpartition Γ).restrict hcover).parts) :
    ∃ B₀ : (pairFamilyComponentFinpartition Γ).parts, B₀.1 ⊓ S = B.1 := by
  classical
  have hBmem :
      B.1 ∈ (((pairFamilyComponentFinpartition Γ).parts.image (fun p => p ⊓ S)).erase ∅) := by
    exact B.2
  have hBimage : B.1 ∈ (pairFamilyComponentFinpartition Γ).parts.image (fun p => p ⊓ S) :=
    Finset.mem_of_mem_erase hBmem
  rcases Finset.mem_image.mp hBimage with ⟨p, hp, hp_eq⟩
  exact ⟨⟨p, hp⟩, hp_eq⟩

/-- Select an ambient component part lying over a block of the restricted
component partition. -/
noncomputable def restrictedComponentAmbientPart
    (Γ : Finset (PairEdge (coordinates q))) {S : Finset (Fin q)}
    (hcover : S ⊆ edgeVertices Γ)
    (B : ((pairFamilyComponentFinpartition Γ).restrict hcover).parts) :
    (pairFamilyComponentFinpartition Γ).parts :=
  Classical.choose (exists_component_part_of_mem_restrict (q := q) Γ hcover B)

theorem restrictedComponentAmbientPart_inf_eq
    (Γ : Finset (PairEdge (coordinates q))) {S : Finset (Fin q)}
    (hcover : S ⊆ edgeVertices Γ)
    (B : ((pairFamilyComponentFinpartition Γ).restrict hcover).parts) :
    (restrictedComponentAmbientPart (q := q) Γ hcover B).1 ⊓ S = B.1 :=
  Classical.choose_spec (exists_component_part_of_mem_restrict (q := q) Γ hcover B)

/-- On covering edge families, partition `S` by ambient connected components of
`Γ`, keeping each full ambient component cluster attached to the restricted
block. -/
noncomputable def supportPartitionAmbientComponentSelector
    (Γ : Finset (PairEdge (coordinates q))) {S : Finset (Fin q)}
    (hcover : S ⊆ edgeVertices Γ) :
    SupportPartitionAmbientClusters (q := q) S :=
  ⟨(pairFamilyComponentFinpartition Γ).restrict hcover,
    fun B =>
      { support := (restrictedComponentAmbientPart (q := q) Γ hcover B).1
        cluster := pairFamilyComponentClusterOfPart Γ
          (restrictedComponentAmbientPart (q := q) Γ hcover B)
        block_subset := by
          intro i hi
          have hmem :
              i ∈ (restrictedComponentAmbientPart (q := q) Γ hcover B).1 ⊓ S := by
            simpa [restrictedComponentAmbientPart_inf_eq (q := q) Γ hcover B] using hi
          exact (Finset.mem_inter.mp hmem).1 }⟩

theorem supportPartitionAmbientComponentSelector_spec
    (Γ : Finset (PairEdge (coordinates q))) {S : Finset (Fin q)}
    (hcover : S ⊆ edgeVertices Γ)
    (B : (supportPartitionAmbientComponentSelector (q := q) Γ hcover).1.parts) :
    ((supportPartitionAmbientComponentSelector (q := q) Γ hcover).2 B).cluster.edges ⊆ Γ ∧
      B.1 ⊆ ((supportPartitionAmbientComponentSelector (q := q) Γ hcover).2 B).support := by
  constructor
  · dsimp [supportPartitionAmbientComponentSelector]
    exact pairFamilyComponentClusterOfPart_edges_subset Γ _
  · exact ((supportPartitionAmbientComponentSelector (q := q) Γ hcover).2 B).block_subset

/-- A pair-edge family induces a support-partition cluster index on its touched
vertices. -/
noncomputable def pairFamilyComponentSupportPartitionIndex
    (Γ : Finset (PairEdge (coordinates q))) :
    SupportPartitionClusters (q := q) (edgeVertices Γ) :=
  ⟨pairFamilyComponentFinpartition Γ, fun B => pairFamilyComponentClusterOfPart Γ B⟩

/-- Blocks in a support-partition cluster index are nonempty by Mathlib's
`Finpartition` convention. -/
theorem supportPartitionClusters_block_nonempty {S : Finset (Fin q)}
    (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts) :
    B.1.Nonempty := by
  exact idx.1.nonempty_of_mem_parts B.2

/-- The block sizes in a support-partition cluster index sum to the ambient
support size. -/
theorem supportPartitionClusters_sum_block_card {S : Finset (Fin q)}
    (idx : SupportPartitionClusters (q := q) S) :
    (∑ B : idx.1.parts, B.1.card) = S.card := by
  rw [← idx.1.sum_card_parts]
  exact Finset.sum_attach idx.1.parts (fun B => B.card)

/-- On a two-point support, a support-partition cluster index has exactly one
block.  Every block carries a pair cluster, hence has cardinality at least two. -/
theorem supportPartitionClusters_parts_card_eq_one_of_support_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : SupportPartitionClusters (q := q) S) :
    idx.1.parts.card = 1 := by
  classical
  have hS_nonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hSempty
    rw [hSempty] at hcard
    simp at hcard
  have hparts_pos : 0 < idx.1.parts.card := by
    exact Finset.card_pos.mpr
      (idx.1.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hS_nonempty))
  have hsum_ge :
      2 * idx.1.parts.card ≤ (∑ B : idx.1.parts, B.1.card) := by
    calc
      2 * idx.1.parts.card = ∑ _B : idx.1.parts, 2 := by
        simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ B : idx.1.parts, B.1.card := by
        refine Finset.sum_le_sum ?_
        intro B _hB
        exact pairCluster_support_card_ge_two_of_nonempty (idx.2 B)
          (supportPartitionClusters_block_nonempty idx B)
  rw [supportPartitionClusters_sum_block_card idx, hcard] at hsum_ge
  omega

/-- On a two-point support, the unique support-partition block is the whole
support.  Singleton blocks cannot occur because each block carries a connected
pair cluster. -/
theorem supportPartitionClusters_block_eq_support_of_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts) :
    B.1 = S := by
  classical
  have hparts : idx.1.parts.card = 1 :=
    supportPartitionClusters_parts_card_eq_one_of_support_card_eq_two
      (q := q) hcard idx
  have hBonly : idx.1.parts = {B.1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact B.2
    · intro C hC
      have hsub : ({B.1, C} : Finset (Finset (Fin q))) ⊆ idx.1.parts := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact B.2
        · exact hC
      have hcard_pair : ({B.1, C} : Finset (Finset (Fin q))).card ≤ 1 := by
        calc
          ({B.1, C} : Finset (Finset (Fin q))).card ≤ idx.1.parts.card :=
            Finset.card_le_card hsub
          _ = 1 := hparts
      by_contra hne
      have hne' : (B.1 : Finset (Fin q)) ≠ C := by
        exact fun h => hne h.symm
      have htwo : ({B.1, C} : Finset (Finset (Fin q))).card = 2 :=
        Finset.card_pair hne'
      omega
  have hsup : idx.1.parts.sup id = S := idx.1.sup_parts
  rw [hBonly] at hsup
  rw [Finset.sup_singleton] at hsup
  exact hsup

/-- The type of blocks of a two-point support-partition cluster has exactly
one element. -/
theorem supportPartitionClusters_parts_univ_eq_singleton_of_card_eq_two
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts) :
    (Finset.univ : Finset idx.1.parts) = {B} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · simp
  · intro C _hC
    apply Subtype.ext
    exact
      (supportPartitionClusters_block_eq_support_of_card_eq_two
        (q := q) hcard idx C).trans
        (supportPartitionClusters_block_eq_support_of_card_eq_two
          (q := q) hcard idx B).symm

/-- The unique block of a support-partition cluster over a two-point support. -/
noncomputable def supportPartitionClustersUniqueBlockOfCardEqTwo
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : SupportPartitionClusters (q := q) S) : idx.1.parts := by
  classical
  have hne : idx.1.parts.Nonempty := by
    have hS : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hSempty
      rw [hSempty] at hcard
      simp at hcard
    exact idx.1.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hS)
  exact ⟨hne.choose, hne.choose_spec⟩

@[simp]
theorem supportPartitionClustersUniqueBlockOfCardEqTwo_support
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : SupportPartitionClusters (q := q) S) :
    (supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx).1 = S := by
  exact supportPartitionClusters_block_eq_support_of_card_eq_two
    (q := q) hcard idx _

/-- Tree-indexed support partitions have the same block-cardinality sum. -/
theorem supportPartitionTrees_sum_block_card {S : Finset (Fin q)}
    (idx : SupportPartitionTrees (q := q) S) :
    (∑ B : idx.1.parts, B.1.card) = S.card := by
  rw [← idx.1.sum_card_parts]
  exact Finset.sum_attach idx.1.parts (fun B => B.card)

/-- Product of connected block contributions over a support partition.  This is
the concrete contribution shape expected after regrouping an edge family by
connected components and then applying the support-level cumulant/Penrose
transform. -/
def supportPartitionClusterProductContribution [AddGroup G] [Fintype G] [DecidableEq G]
    (blockContribution : PairClusterContribution (G := G) (q := q)) :
    SupportIndexedContribution (G := G) (q := q) (SupportPartitionClusters (q := q)) :=
  fun _S idx y =>
    ∏ B : idx.1.parts, blockContribution B.1 (idx.2 B) y

/-- On a two-point support, a support-partition product is the contribution of
its unique block. -/
theorem supportPartitionClusterProductContribution_cardTwo
    [AddGroup G] [Fintype G] [DecidableEq G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts)
    (y : Fin q → G) :
    supportPartitionClusterProductContribution (G := G) (q := q)
        blockContribution S idx y =
      blockContribution B.1 (idx.2 B) y := by
  classical
  unfold supportPartitionClusterProductContribution
  rw [supportPartitionClusters_parts_univ_eq_singleton_of_card_eq_two
    (q := q) hcard idx B]
  simp

/-- Expand a support-partition product after each block contribution has been
evaluated as a finite sum.  This is the pure algebraic product-of-sums step in
the future global atomized evaluation. -/
theorem supportPartitionClusterProductContribution_eq_sum_pi_blockValues
    [AddGroup G] [Fintype G] [DecidableEq G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (BlockTerm : {S : Finset (Fin q)} →
      (idx : SupportPartitionClusters (q := q) S) → idx.1.parts → Type*)
    [blockTermFintype : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts),
      Fintype (BlockTerm idx B)]
    (blockValue : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts),
      BlockTerm idx B → (Fin q → G) → ℝ)
    (hblockEval : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts)
      (y : Fin q → G),
      blockContribution B.1 (idx.2 B) y =
        ∑ tB : BlockTerm idx B, blockValue idx B tB y)
    {S : Finset (Fin q)} (idx : SupportPartitionClusters (q := q) S)
    (y : Fin q → G) :
    supportPartitionClusterProductContribution (G := G) (q := q)
        blockContribution S idx y =
      ∑ t : (B : idx.1.parts) → BlockTerm idx B,
        ∏ B : idx.1.parts, blockValue idx B (t B) y := by
  classical
  unfold supportPartitionClusterProductContribution
  calc
    (∏ B : idx.1.parts, blockContribution B.1 (idx.2 B) y) =
        ∏ B : idx.1.parts, ∑ tB : BlockTerm idx B, blockValue idx B tB y := by
          refine Finset.prod_congr rfl ?_
          intro B _hB
          rw [hblockEval idx B y]
    _ = ∑ t : (B : idx.1.parts) → BlockTerm idx B,
          ∏ B : idx.1.parts, blockValue idx B (t B) y := by
          rw [Fintype.prod_sum]

/-- Product-of-block-sums expansion with scalar coefficients separated from the
block values. -/
theorem supportPartitionClusterProductContribution_eq_sum_pi_blockCoeff_mul_values
    [AddGroup G] [Fintype G] [DecidableEq G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (BlockTerm : {S : Finset (Fin q)} →
      (idx : SupportPartitionClusters (q := q) S) → idx.1.parts → Type*)
    [blockTermFintype : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts),
      Fintype (BlockTerm idx B)]
    (blockCoeff : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts),
      BlockTerm idx B → ℝ)
    (blockValue : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts),
      BlockTerm idx B → (Fin q → G) → ℝ)
    (hblockEval : ∀ {S : Finset (Fin q)}
      (idx : SupportPartitionClusters (q := q) S) (B : idx.1.parts)
      (y : Fin q → G),
      blockContribution B.1 (idx.2 B) y =
        ∑ tB : BlockTerm idx B, blockCoeff idx B tB * blockValue idx B tB y)
    {S : Finset (Fin q)} (idx : SupportPartitionClusters (q := q) S)
    (y : Fin q → G) :
    supportPartitionClusterProductContribution (G := G) (q := q)
        blockContribution S idx y =
      ∑ t : (B : idx.1.parts) → BlockTerm idx B,
        (∏ B : idx.1.parts, blockCoeff idx B (t B)) *
          ∏ B : idx.1.parts, blockValue idx B (t B) y := by
  classical
  rw [supportPartitionClusterProductContribution_eq_sum_pi_blockValues
    (G := G) (q := q) blockContribution BlockTerm
    (fun idx B tB y => blockCoeff idx B tB * blockValue idx B tB y)
    hblockEval idx y]
  refine Finset.sum_congr rfl ?_
  intro t _ht
  rw [← Finset.prod_mul_distrib]

/-- Weighted support-partition product contribution.

The coefficient may depend on the whole support partition and all of its block
clusters.  This keeps the interface expressive enough for an Ursell/Penrose
resummation whose Möbius coefficient is not block-local. -/
def supportPartitionWeightedClusterProductContribution
    [AddGroup G] [Fintype G] [DecidableEq G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q)) :
    SupportIndexedContribution (G := G) (q := q) (SupportPartitionClusters (q := q)) :=
  fun S idx y =>
    weight S idx *
      supportPartitionClusterProductContribution (G := G) (q := q) blockContribution S idx y

@[simp]
theorem supportPartitionWeightedClusterProductContribution_one
    [AddGroup G] [Fintype G] [DecidableEq G]
    (blockContribution : PairClusterContribution (G := G) (q := q)) :
    supportPartitionWeightedClusterProductContribution (G := G) (q := q)
        (fun _S _idx => (1 : ℝ)) blockContribution =
      supportPartitionClusterProductContribution (G := G) (q := q) blockContribution := by
  funext S idx y
  simp [supportPartitionWeightedClusterProductContribution]

/-- Standard Ursell/Möbius coefficient for collapsing a support partition to one
connected cumulant: `(-1)^(m-1) (m-1)!`, where `m` is the number of blocks. -/
def supportPartitionUrsellWeight (S : Finset (Fin q))
    (idx : SupportPartitionClusters (q := q) S) : ℝ :=
  (-1 : ℝ) ^ (idx.1.parts.card - 1) *
    (Nat.factorial (idx.1.parts.card - 1) : ℝ)

@[simp]
theorem abs_supportPartitionUrsellWeight (S : Finset (Fin q))
    (idx : SupportPartitionClusters (q := q) S) :
    |supportPartitionUrsellWeight (q := q) S idx| =
      (Nat.factorial (idx.1.parts.card - 1) : ℝ) := by
  unfold supportPartitionUrsellWeight
  simp [abs_mul, abs_of_nonneg]

/-- Crude but useful coefficient-size bound for the support-partition Ursell
weight.  The number of blocks in a finpartition is at most the support size. -/
theorem abs_supportPartitionUrsellWeight_le_factorial_card (S : Finset (Fin q))
    (idx : SupportPartitionClusters (q := q) S) :
    |supportPartitionUrsellWeight (q := q) S idx| ≤ (Nat.factorial S.card : ℝ) := by
  rw [abs_supportPartitionUrsellWeight]
  have hle : idx.1.parts.card - 1 ≤ S.card := by
    have hparts := idx.1.card_parts_le_card
    omega
  exact_mod_cast Nat.factorial_le hle

@[simp]
theorem supportPartitionClusterProductContribution_pairFamilyComponentSupportPartitionIndex
    [AddGroup G] [Fintype G] [DecidableEq G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (Γ : Finset (PairEdge (coordinates q))) (y : Fin q → G) :
    supportPartitionClusterProductContribution (G := G) (q := q) blockContribution
        (edgeVertices Γ) (pairFamilyComponentSupportPartitionIndex (q := q) Γ) y =
      ∏ B : (pairFamilyComponentFinpartition Γ).parts,
        blockContribution B.1 (pairFamilyComponentClusterOfPart (q := q) Γ B) y := by
  rfl

/-- The hard support-partition resummation leaf for a weighted
Penrose/Ursell contribution family. -/
def SupportPartitionWeightedResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S,
      supportPartitionWeightedClusterProductContribution (G := G) (q := q)
        weight blockContribution S idx y

/-- The concrete Ursell-weight version of the support-partition resummation
leaf. -/
def SupportPartitionUrsellResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  SupportPartitionWeightedResummationGeTwo (G := G) (q := q)
    (supportPartitionUrsellWeight (q := q)) blockContribution

/-- Covering-fiber resummation implies the weighted support-partition
resummation leaf.

This is the finite reindexing bridge for the Penrose/Ursell route.  It removes
non-covering pair-edge families using the existing ANOVA off-support vanishing
lemma, then splits the remaining finite sum into fibers of the supplied
support-partition selector.  The actual Mayer/Ursell algebra is isolated in the
`hfiber` premise. -/
theorem supportPartitionWeightedResummationGeTwo_of_coveringFiber_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionClusters (q := q) S)]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionClusters (q := q) S)
    (hfiber : ∀ S (_hSpow : S ∈ (coordinates q).powerset)
      (hS : S.Nonempty) (hge : 2 ≤ S.card),
      ∀ idx : SupportPartitionClusters (q := q) S,
        (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
        fun y =>
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) weight blockContribution S idx y) :
    SupportPartitionWeightedResummationGeTwo (G := G) (q := q)
      weight blockContribution := by
  intro S hSpow hS hge
  classical
  funext y
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  calc
    (∑ Γ ∈ A, term Γ)
        = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then term Γ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro Γ _hΓ
            by_cases hcover : S ⊆ edgeVertices Γ
            · simp [hcover]
            · have hzero : term Γ = 0 := by
                dsimp [term]
                rw [← normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
                rw [anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
                  (G := G) (q := q) Γ hcover]
              simp [hcover, hzero]
    _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
          rw [Finset.sum_filter]
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
            term Γ := by
          calc
            (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ)
                = ∑ idx : SupportPartitionClusters (q := q) S,
                    ∑ Γ ∈ (A.filter (fun Γ => S ⊆ edgeVertices Γ)).filter
                        (fun Γ => select S hS hge Γ = idx),
                      term Γ := by
                      rw [Finset.sum_fiberwise]
            _ = ∑ idx : SupportPartitionClusters (q := q) S,
                  ∑ Γ ∈ A.filter
                      (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
                    term Γ := by
                  refine Finset.sum_congr rfl ?_
                  intro idx _hidx
                  refine Finset.sum_congr ?_ ?_
                  · ext Γ
                    simp [and_assoc]
                  · intro Γ _hΓ
                    rfl
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) weight blockContribution S idx y := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          exact congrFun (hfiber S hSpow hS hge idx) y

/-- Fixed-support selector/fiber bridge for the weighted covering
contraction.  This is the local version of the finite reindexing step: once a
selector is fixed on covering edge families over `S`, it suffices to prove the
identity on each selector fiber. -/
theorem supportPartitionCoveringWeightedSupportContraction_of_selected_fibers
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q))
    [DecidableEq (SupportPartitionClusters (q := q) S)]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (select : Finset (PairEdge (coordinates q)) → SupportPartitionClusters (q := q) S)
    (hfiber : ∀ idx : SupportPartitionClusters (q := q) S,
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
      fun y =>
        supportPartitionWeightedClusterProductContribution
          (G := G) (q := q) weight blockContribution S idx y) :
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S,
      supportPartitionWeightedClusterProductContribution
        (G := G) (q := q) weight blockContribution S idx y := by
  funext y
  classical
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  calc
    (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ)
        = ∑ idx : SupportPartitionClusters (q := q) S,
            ∑ Γ ∈ (A.filter (fun Γ => S ⊆ edgeVertices Γ)).filter
                (fun Γ => select Γ = idx),
              term Γ := by
              rw [Finset.sum_fiberwise
                (s := A.filter (fun Γ => S ⊆ edgeVertices Γ))
                (g := select) (f := term)]
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
            term Γ := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          refine Finset.sum_congr ?_ ?_
          · ext Γ
            simp [and_assoc]
          · intro Γ _hΓ
            rfl
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) weight blockContribution S idx y := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          exact congrFun (hfiber idx) y

/-- Generic fixed-support selector/fiber reindexing.  This is the same finite
sum argument as `supportPartitionCoveringWeightedSupportContraction_of_selected_fibers`,
but with the indexed target contribution supplied directly.  It is useful when
the correct target has already been centered by an ANOVA projection and is not
syntactically a raw weighted support-partition product. -/
theorem supportPartitionCoveringSupportContraction_of_selected_fibers
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q))
    [DecidableEq (SupportPartitionClusters (q := q) S)]
    (target : SupportPartitionClusters (q := q) S → (Fin q → G) → ℝ)
    (select : Finset (PairEdge (coordinates q)) → SupportPartitionClusters (q := q) S)
    (hfiber : ∀ idx : SupportPartitionClusters (q := q) S,
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
      fun y => target idx y) :
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S, target idx y := by
  funext y
  classical
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  calc
    (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ)
        = ∑ idx : SupportPartitionClusters (q := q) S,
            ∑ Γ ∈ (A.filter (fun Γ => S ⊆ edgeVertices Γ)).filter
                (fun Γ => select Γ = idx),
              term Γ := by
              rw [Finset.sum_fiberwise
                (s := A.filter (fun Γ => S ⊆ edgeVertices Γ))
                (g := select) (f := term)]
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
            term Γ := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          refine Finset.sum_congr ?_ ?_
          · ext Γ
            simp [and_assoc]
          · intro Γ _hΓ
            rfl
    _ = ∑ idx : SupportPartitionClusters (q := q) S, target idx y := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          exact congrFun (hfiber idx) y

/-- Named child obligation for a weighted support-partition resummation leaf:
produce a selector from covering pair-edge families to support-partition indices
and prove the fiber identity for every selected index. -/
def SupportPartitionWeightedCoveringFiberResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionClusters (q := q) S)]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∃ select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionClusters (q := q) S,
    ∀ S (_hSpow : S ∈ (coordinates q).powerset)
      (hS : S.Nonempty) (hge : 2 ≤ S.card),
      ∀ idx : SupportPartitionClusters (q := q) S,
        (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
        fun y =>
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) weight blockContribution S idx y

/-- Existential selector form of the weighted support-partition resummation
bridge. -/
theorem supportPartitionWeightedResummationGeTwo_of_exists_coveringFiber_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionClusters (q := q) S)]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hselect : SupportPartitionWeightedCoveringFiberResummationGeTwo
      (G := G) (q := q) weight blockContribution) :
    SupportPartitionWeightedResummationGeTwo (G := G) (q := q)
      weight blockContribution := by
  rcases hselect with ⟨select, hfiber⟩
  exact supportPartitionWeightedResummationGeTwo_of_coveringFiber_resummation
    (G := G) (q := q) weight blockContribution select hfiber

/-- Concrete Ursell-weight version of the covering-fiber resummation bridge. -/
theorem supportPartitionUrsellResummationGeTwo_of_coveringFiber_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionClusters (q := q) S)]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionClusters (q := q) S)
    (hfiber : ∀ S (_hSpow : S ∈ (coordinates q).powerset)
      (hS : S.Nonempty) (hge : 2 ≤ S.card),
      ∀ idx : SupportPartitionClusters (q := q) S,
        (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
        fun y =>
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) (supportPartitionUrsellWeight (q := q))
            blockContribution S idx y) :
    SupportPartitionUrsellResummationGeTwo (G := G) (q := q)
      blockContribution := by
  exact supportPartitionWeightedResummationGeTwo_of_coveringFiber_resummation
    (G := G) (q := q) (supportPartitionUrsellWeight (q := q))
    blockContribution select hfiber

/-- Named child obligation for the concrete Ursell resummation leaf: produce a
selector from covering pair-edge families to support-partition indices and prove
the fiber identity for every selected index. -/
def SupportPartitionUrsellCoveringFiberResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionClusters (q := q) S)]
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∃ select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionClusters (q := q) S,
    ∀ S (_hSpow : S ∈ (coordinates q).powerset)
      (hS : S.Nonempty) (hge : 2 ≤ S.card),
      ∀ idx : SupportPartitionClusters (q := q) S,
        (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
        fun y =>
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) (supportPartitionUrsellWeight (q := q))
            blockContribution S idx y

/-- Source-faithful selector obligation into ambient support-partition clusters.
This is the selector branch before the Penrose/Ursell contraction removes
off-support vertices. -/
def SupportPartitionAmbientCoveringSelector : Prop :=
  ∃ select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionAmbientClusters (q := q) S,
    ∀ S (hS : S.Nonempty) (hge : 2 ≤ S.card)
      (Γ : Finset (PairEdge (coordinates q))),
      S ⊆ edgeVertices Γ →
        ∀ B : (select S hS hge Γ).1.parts,
          ((select S hS hge Γ).2 B).cluster.edges ⊆ Γ ∧
            B.1 ⊆ ((select S hS hge Γ).2 B).support

theorem supportPartitionAmbientCoveringSelector :
    SupportPartitionAmbientCoveringSelector (q := q) := by
  classical
  refine ⟨fun S hS hge Γ =>
    if hcover : S ⊆ edgeVertices Γ then
      supportPartitionAmbientComponentSelector (q := q) Γ hcover
    else
      supportPartitionAmbientFallback (q := q) S hS hge, ?_⟩
  intro S hS hge Γ hcover B
  revert B
  simp [hcover]
  intro B hB
  convert supportPartitionAmbientComponentSelector_spec (q := q) Γ hcover ⟨B, hB⟩ <;>
    simp [hcover]

/-- The canonical ambient selector used by the ambient-fiber branch. -/
noncomputable def supportPartitionAmbientCoveringSelect :
    (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionAmbientClusters (q := q) S :=
  Classical.choose (supportPartitionAmbientCoveringSelector (q := q))

theorem supportPartitionAmbientCoveringSelect_spec
    (S : Finset (Fin q)) (hS : S.Nonempty) (hge : 2 ≤ S.card)
    (Γ : Finset (PairEdge (coordinates q))) (hcover : S ⊆ edgeVertices Γ)
    (B : (supportPartitionAmbientCoveringSelect (q := q) S hS hge Γ).1.parts) :
    ((supportPartitionAmbientCoveringSelect (q := q) S hS hge Γ).2 B).cluster.edges ⊆ Γ ∧
      B.1 ⊆ ((supportPartitionAmbientCoveringSelect (q := q) S hS hge Γ).2 B).support :=
  Classical.choose_spec (supportPartitionAmbientCoveringSelector (q := q))
    S hS hge Γ hcover B

/-- Ambient-cluster fiber resummation: the finite covering-family sum has been
split by a source-faithful selector that still remembers off-support ambient
components. -/
def SupportPartitionAmbientFiberResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (ambientContribution : SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q))) : Prop :=
  ∃ select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionAmbientClusters (q := q) S,
    ∀ S (_hSpow : S ∈ (coordinates q).powerset)
      (hS : S.Nonempty) (hge : 2 ≤ S.card),
      ∀ idx : SupportPartitionAmbientClusters (q := q) S,
        (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
        fun y => ambientContribution S idx y

/-- The exact ambient fiber contribution induced by a concrete selector.  This
is only a reindexing object: all Penrose/Ursell cancellation remains in the
separate ambient-to-Ursell contraction obligation. -/
noncomputable def supportPartitionAmbientFiberContribution
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionAmbientClusters (q := q) S) :
    SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q)) :=
  fun S idx y =>
    if hS : S.Nonempty then
      if hge : 2 ≤ S.card then
        ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
      else
        0
    else
      0

theorem supportPartitionAmbientFiberResummationGeTwo_of_select
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card →
        Finset (PairEdge (coordinates q)) → SupportPartitionAmbientClusters (q := q) S) :
    SupportPartitionAmbientFiberResummationGeTwo (G := G) (q := q)
      (supportPartitionAmbientFiberContribution (G := G) (q := q) select) := by
  refine ⟨select, ?_⟩
  intro S _hSpow hS hge idx
  funext y
  simp [supportPartitionAmbientFiberContribution, hS, hge]

/-- Canonical ambient fiber contribution generated by the source-faithful
covering selector. -/
noncomputable def supportPartitionCanonicalAmbientFiberContribution
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)] :
    SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q)) :=
  supportPartitionAmbientFiberContribution (G := G) (q := q)
    (supportPartitionAmbientCoveringSelect (q := q))

theorem supportPartitionCanonicalAmbientFiberResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)] :
    SupportPartitionAmbientFiberResummationGeTwo (G := G) (q := q)
      (supportPartitionCanonicalAmbientFiberContribution (G := G) (q := q)) := by
  exact supportPartitionAmbientFiberResummationGeTwo_of_select (G := G) (q := q)
    (supportPartitionAmbientCoveringSelect (q := q))

/-- The later Ursell/Penrose contraction obligation: after summing over the
ambient decorated indices, the result is the standard Ursell-weighted
support-partition contribution. -/
def SupportPartitionAmbientToUrsellContractionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), Fintype (SupportPartitionAmbientClusters (q := q) S)]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (ambientContribution : SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q)))
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (fun y => ∑ idx : SupportPartitionAmbientClusters (q := q) S,
      ambientContribution S idx y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S,
      supportPartitionWeightedClusterProductContribution
        (G := G) (q := q) (supportPartitionUrsellWeight (q := q))
        blockContribution S idx y

/-- Weighted version of the ambient-to-support contraction obligation.  This is
the source-faithful form needed by normalized/certified branches whose
partition coefficient is not just the bare Ursell coefficient. -/
def SupportPartitionAmbientToWeightedContractionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), Fintype (SupportPartitionAmbientClusters (q := q) S)]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (ambientContribution : SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q)))
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (fun y => ∑ idx : SupportPartitionAmbientClusters (q := q) S,
      ambientContribution S idx y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S,
      supportPartitionWeightedClusterProductContribution
        (G := G) (q := q) weight blockContribution S idx y

/-- Canonical remaining contraction obligation after fixing the source-faithful
ambient covering selector and its exact fiber contribution. -/
def SupportPartitionCanonicalAmbientToUrsellContractionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  SupportPartitionAmbientToUrsellContractionGeTwo (G := G) (q := q)
    (supportPartitionCanonicalAmbientFiberContribution (G := G) (q := q))
    blockContribution

/-- Canonical weighted contraction after fixing the source-faithful ambient
covering selector and its exact fiber contribution. -/
def SupportPartitionCanonicalAmbientToWeightedContractionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  SupportPartitionAmbientToWeightedContractionGeTwo (G := G) (q := q)
    (supportPartitionCanonicalAmbientFiberContribution (G := G) (q := q))
    weight blockContribution

/-- The remaining covering-family Ursell cancellation identity after all
off-support cleanup and ambient-fiber reindexing have been discharged. -/
def SupportPartitionCoveringUrsellContractionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S,
      supportPartitionWeightedClusterProductContribution
        (G := G) (q := q) (supportPartitionUrsellWeight (q := q))
        blockContribution S idx y

/-- Weighted version of the covering-family cancellation identity.  This is an
interface, not a generic theorem: the identity is meaningful only for a
matched weight/block-contribution pair. -/
def SupportPartitionCoveringWeightedContractionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
    fun y => ∑ idx : SupportPartitionClusters (q := q) S,
      supportPartitionWeightedClusterProductContribution
        (G := G) (q := q) weight blockContribution S idx y

/-- Summing the canonical ambient fiber contribution over ambient indices
recovers exactly the covering edge-family sum.  This is finite reindexing only;
it contains no Ursell/Penrose cancellation. -/
theorem sum_supportPartitionCanonicalAmbientFiberContribution_eq_covering
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (hS : S.Nonempty) (hge : 2 ≤ S.card) :
    (fun y => ∑ idx : SupportPartitionAmbientClusters (q := q) S,
      supportPartitionCanonicalAmbientFiberContribution (G := G) (q := q) S idx y) =
    fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y := by
  classical
  funext y
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  let select := supportPartitionAmbientCoveringSelect (q := q)
  calc
    (∑ idx : SupportPartitionAmbientClusters (q := q) S,
      supportPartitionCanonicalAmbientFiberContribution (G := G) (q := q) S idx y)
        = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
            ∑ Γ ∈ A.filter
                (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
              term Γ := by
            simp [supportPartitionCanonicalAmbientFiberContribution,
              supportPartitionAmbientFiberContribution, A, term, select, hS, hge]
    _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
          ∑ Γ ∈ (A.filter (fun Γ => S ⊆ edgeVertices Γ)).filter
              (fun Γ => select S hS hge Γ = idx),
            term Γ := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          refine Finset.sum_congr ?_ ?_
          · ext Γ
            simp [and_assoc]
          · intro Γ _hΓ
            rfl
    _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
          rw [Finset.sum_fiberwise
            (s := A.filter (fun Γ => S ⊆ edgeVertices Γ))
            (g := fun Γ => select S hS hge Γ) (f := term)]

/-- The canonical ambient contraction follows from the genuine covering-to-Ursell
identity.  Everything before this theorem is finite reindexing; the premise is
the remaining Mayer/Ursell cancellation target. -/
theorem supportPartitionCanonicalAmbientToUrsellContractionGeTwo_of_coveringUrsell
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hcovering : SupportPartitionCoveringUrsellContractionGeTwo
      (G := G) (q := q) blockContribution) :
    SupportPartitionCanonicalAmbientToUrsellContractionGeTwo
      (G := G) (q := q) blockContribution := by
  intro S hSpow hS hge
  rw [sum_supportPartitionCanonicalAmbientFiberContribution_eq_covering
    (G := G) (q := q) S hS hge]
  exact hcovering S hSpow hS hge

/-- The canonical weighted ambient contraction follows from the matched
weighted covering-family contraction identity.  This theorem is only finite
reindexing; the premise is the genuine Mayer/Ursell cancellation target. -/
theorem supportPartitionCanonicalAmbientToWeightedContractionGeTwo_of_coveringWeighted
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hcovering : SupportPartitionCoveringWeightedContractionGeTwo
      (G := G) (q := q) weight blockContribution) :
    SupportPartitionCanonicalAmbientToWeightedContractionGeTwo
      (G := G) (q := q) weight blockContribution := by
  intro S hSpow hS hge
  rw [sum_supportPartitionCanonicalAmbientFiberContribution_eq_covering
    (G := G) (q := q) S hS hge]
  exact hcovering S hSpow hS hge

/-- Ambient fibers plus an ambient-to-weighted contraction recover the weighted
support-partition resummation leaf. -/
theorem supportPartitionWeightedResummationGeTwo_of_ambientFiber_weightedContraction
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), Fintype (SupportPartitionAmbientClusters (q := q) S)]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (ambientContribution : SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q)))
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hfiber : SupportPartitionAmbientFiberResummationGeTwo
      (G := G) (q := q) ambientContribution)
    (hcontract : SupportPartitionAmbientToWeightedContractionGeTwo
      (G := G) (q := q) ambientContribution weight blockContribution) :
    SupportPartitionWeightedResummationGeTwo (G := G) (q := q)
      weight blockContribution := by
  rcases hfiber with ⟨select, hfiber⟩
  intro S hSpow hS hge
  classical
  funext y
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  calc
    (∑ Γ ∈ A, term Γ)
        = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then term Γ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro Γ _hΓ
            by_cases hcover : S ⊆ edgeVertices Γ
            · simp [hcover]
            · have hzero : term Γ = 0 := by
                dsimp [term]
                rw [← normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
                rw [anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
                  (G := G) (q := q) Γ hcover]
              simp [hcover, hzero]
    _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
          rw [Finset.sum_filter]
    _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
          ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
            term Γ := by
          calc
            (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ)
                = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
                    ∑ Γ ∈ (A.filter (fun Γ => S ⊆ edgeVertices Γ)).filter
                        (fun Γ => select S hS hge Γ = idx),
                      term Γ := by
                      rw [Finset.sum_fiberwise
                        (s := A.filter (fun Γ => S ⊆ edgeVertices Γ))
                        (g := fun Γ => select S hS hge Γ) (f := term)]
            _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
                  ∑ Γ ∈ A.filter
                      (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
                    term Γ := by
                  refine Finset.sum_congr rfl ?_
                  intro idx _hidx
                  refine Finset.sum_congr ?_ ?_
                  · ext Γ
                    simp [and_assoc]
                  · intro Γ _hΓ
                    rfl
    _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
          ambientContribution S idx y := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          exact congrFun (hfiber S hSpow hS hge idx) y
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) weight blockContribution S idx y := by
          exact congrFun (hcontract S hSpow hS hge) y

/-- Ambient selector fibers plus the ambient-to-Ursell contraction recover the
standard concrete Ursell resummation leaf. -/
theorem supportPartitionUrsellResummationGeTwo_of_ambientFiber_contraction
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), Fintype (SupportPartitionAmbientClusters (q := q) S)]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionAmbientClusters (q := q) S)]
    (ambientContribution : SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionAmbientClusters (q := q)))
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hfiber : SupportPartitionAmbientFiberResummationGeTwo
      (G := G) (q := q) ambientContribution)
    (hcontract : SupportPartitionAmbientToUrsellContractionGeTwo
      (G := G) (q := q) ambientContribution blockContribution) :
    SupportPartitionUrsellResummationGeTwo (G := G) (q := q)
      blockContribution := by
  rcases hfiber with ⟨select, hfiber⟩
  intro S hSpow hS hge
  classical
  funext y
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  calc
    (∑ Γ ∈ A, term Γ)
        = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then term Γ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro Γ _hΓ
            by_cases hcover : S ⊆ edgeVertices Γ
            · simp [hcover]
            · have hzero : term Γ = 0 := by
                dsimp [term]
                rw [← normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
                rw [anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
                  (G := G) (q := q) Γ hcover]
              simp [hcover, hzero]
    _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
          rw [Finset.sum_filter]
    _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
          ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
            term Γ := by
          calc
            (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ)
                = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
                    ∑ Γ ∈ (A.filter (fun Γ => S ⊆ edgeVertices Γ)).filter
                        (fun Γ => select S hS hge Γ = idx),
                      term Γ := by
                      rw [Finset.sum_fiberwise]
            _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
                  ∑ Γ ∈ A.filter
                      (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
                    term Γ := by
                  refine Finset.sum_congr rfl ?_
                  intro idx _hidx
                  refine Finset.sum_congr ?_ ?_
                  · ext Γ
                    simp [and_assoc]
                  · intro Γ _hΓ
                    rfl
    _ = ∑ idx : SupportPartitionAmbientClusters (q := q) S,
          ambientContribution S idx y := by
          refine Finset.sum_congr rfl ?_
          intro idx _hidx
          exact congrFun (hfiber S hSpow hS hge idx) y
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          supportPartitionWeightedClusterProductContribution
            (G := G) (q := q) (supportPartitionUrsellWeight (q := q))
            blockContribution S idx y := by
          exact congrFun (hcontract S hSpow hS hge) y

/-- Existential selector form of the concrete Ursell resummation bridge.

The concrete selector is part of the future Penrose/Ursell contraction, so this
wrapper keeps the parent resummation leaf stable while exposing the exact child
obligation: produce a selector and prove the fiber identity for it. -/
theorem supportPartitionUrsellResummationGeTwo_of_exists_coveringFiber_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (SupportPartitionClusters (q := q) S)]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hselect : SupportPartitionUrsellCoveringFiberResummationGeTwo
      (G := G) (q := q) blockContribution) :
    SupportPartitionUrsellResummationGeTwo (G := G) (q := q)
      blockContribution := by
  rcases hselect with ⟨select, hfiber⟩
  exact supportPartitionUrsellResummationGeTwo_of_coveringFiber_resummation
    (G := G) (q := q) blockContribution select hfiber

/-- Generic ge-two expansion certificate for the support-indexed Penrose/Ursell
route.  This is the expansion shape that remains source-faithful even when
disconnected edge-family components survive inside a support-level cumulant. -/
def SupportIndexedExpansionGeTwo [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (Index : Finset (Fin q) → Type*)
    [∀ S : Finset (Fin q), Fintype (Index S)]
    (contribution : SupportIndexedContribution (G := G) (q := q) Index) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    anovaComponent S (xopError (G := G) (q := q)) =
      fun y => ∑ i : Index S, contribution S i y

/-- A concrete component-factorized pair-family resummation gives the corrected
support-partition Penrose/Ursell expansion interface.

The `hresum` hypothesis is the source-faithful hard step: it must regroup the
already pair-level Mayer-expanded, component-factorized edge-family terms into
support partitions.  This theorem deliberately does not perform any raw
colored-bond KP argument. -/
theorem supportIndexedExpansionGeTwo_of_componentFactorized_supportPartition_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hresum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
      fun y => ∑ idx : SupportPartitionClusters (q := q) S,
        supportPartitionClusterProductContribution (G := G) (q := q)
          blockContribution S idx y) :
    SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q))
      (supportPartitionClusterProductContribution (G := G) (q := q) blockContribution) := by
  intro S hSpow hS hge
  rw [anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty (G := G) (q := q) hS]
  have hsum :
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (normalizedPairFamilyTerm (G := G) Γ) y) =
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) := by
    funext y
    refine Finset.sum_congr rfl ?_
    intro Γ _hΓ
    rw [normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
  rw [hsum]
  exact hresum S hSpow hS hge

/-- Weighted variant of the component-factorized support-partition resummation
adapter.  This is the source-faithful shape when the Penrose/Ursell coefficient
depends on the whole support partition rather than on independent blocks. -/
theorem supportIndexedExpansionGeTwo_of_componentFactorized_weightedSupportPartition_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hresum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
      fun y => ∑ idx : SupportPartitionClusters (q := q) S,
        supportPartitionWeightedClusterProductContribution (G := G) (q := q)
          weight blockContribution S idx y) :
    SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q))
      (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
        weight blockContribution) := by
  intro S hSpow hS hge
  rw [anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty (G := G) (q := q) hS]
  have hsum :
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (normalizedPairFamilyTerm (G := G) Γ) y) =
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) := by
    funext y
    refine Finset.sum_congr rfl ?_
    intro Γ _hΓ
    rw [normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
  rw [hsum]
  exact hresum S hSpow hS hge

/-- Centered weighted variant of the component-factorized support-partition
resummation adapter.  This is the source-faithful shape when the fiber
identity is ANOVA-centered on both sides: the indexed contribution is itself
`anovaComponent S` of the weighted support-partition product. -/
theorem supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedSupportPartition_resummation
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hresum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
      fun y => ∑ idx : SupportPartitionClusters (q := q) S,
        anovaComponent S
          (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
            weight blockContribution S idx) y) :
    SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q))
      (fun S idx => anovaComponent S
        (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
          weight blockContribution S idx)) := by
  intro S hSpow hS hge
  rw [anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty (G := G) (q := q) hS]
  have hsum :
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (normalizedPairFamilyTerm (G := G) Γ) y) =
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) := by
    funext y
    refine Finset.sum_congr rfl ?_
    intro Γ _hΓ
    rw [normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
  rw [hsum]
  exact hresum S hSpow hS hge

/-- Covering-filtered version of
`supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedSupportPartition_resummation`.
Off-support edge families are removed using the existing ANOVA vanishing lemma,
while the indexed contribution remains centered. -/
theorem supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedCoveringContraction
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hcovering : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y) =
      fun y => ∑ idx : SupportPartitionClusters (q := q) S,
        anovaComponent S
          (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
            weight blockContribution S idx) y) :
    SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q))
      (fun S idx => anovaComponent S
        (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
          weight blockContribution S idx)) := by
  refine supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedSupportPartition_resummation
    (G := G) (q := q) weight blockContribution ?_
  intro S hSpow hS hge
  funext y
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) y
  calc
    (∑ Γ ∈ A, term Γ)
        = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then term Γ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro Γ _hΓ
            by_cases hcover : S ⊆ edgeVertices Γ
            · simp [hcover]
            · have hzero : term Γ = 0 := by
                dsimp [term]
                rw [← normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
                rw [anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
                  (G := G) (q := q) Γ hcover]
              simp [hcover, hzero]
    _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
          rw [Finset.sum_filter]
    _ = ∑ idx : SupportPartitionClusters (q := q) S,
          anovaComponent S
            (supportPartitionWeightedClusterProductContribution
              (G := G) (q := q) weight blockContribution S idx) y := by
          exact congrFun (hcovering S hSpow hS hge) y

/-- Named-obligation wrapper for the weighted support-partition resummation
leaf. -/
theorem supportIndexedExpansionGeTwo_of_weightedResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (weight : (S : Finset (Fin q)) → SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hresum : SupportPartitionWeightedResummationGeTwo (G := G) (q := q)
      weight blockContribution) :
    SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q))
      (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
        weight blockContribution) := by
  exact supportIndexedExpansionGeTwo_of_componentFactorized_weightedSupportPartition_resummation
    (G := G) (q := q) weight blockContribution hresum

/-- Named-obligation wrapper for the concrete Ursell-weight resummation leaf. -/
theorem supportIndexedExpansionGeTwo_of_ursellResummationGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (blockContribution : PairClusterContribution (G := G) (q := q))
    (hresum : SupportPartitionUrsellResummationGeTwo (G := G) (q := q)
      blockContribution) :
    SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q))
      (supportPartitionWeightedClusterProductContribution (G := G) (q := q)
        (supportPartitionUrsellWeight (q := q)) blockContribution) := by
  exact supportIndexedExpansionGeTwo_of_weightedResummationGeTwo
    (G := G) (q := q) (supportPartitionUrsellWeight (q := q)) blockContribution hresum

/-- Support-indexed activity certificate for a ge-two Penrose/Ursell expansion. -/
def SupportIndexedActivityBoundGeTwo [AddGroup G] [Fintype G] [DecidableEq G]
    (Index : Finset (Fin q) → Type*) [∀ S : Finset (Fin q), Fintype (Index S)]
    (contribution : SupportIndexedContribution (G := G) (q := q) Index)
    (localActivity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (∑ i : Index S, visibleL1 (contribution S i)) ≤ localActivity S.card

/-- The corrected support-indexed Penrose/Ursell endpoint implies the existing
component activity interface. -/
theorem componentActivityBound_of_supportIndexedExpansionGeTwo
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    {contribution : SupportIndexedContribution (G := G) (q := q) Index}
    {localActivity : Nat → ℝ}
    (hexp : SupportIndexedExpansionGeTwo (G := G) (q := q) Index contribution)
    (hactivity : SupportIndexedActivityBoundGeTwo (G := G) (q := q)
      Index contribution localActivity)
    (hzero : visibleL1 (anovaComponent ∅ (xopError (G := G) (q := q))) ≤
      localActivity 0)
    (hsingle : ∀ i : Fin q,
      visibleL1 (anovaComponent {i} (xopError (G := G) (q := q))) ≤
        localActivity 1) :
    RandomSystems.Applications.XoP.ANOVA.ComponentActivityBound
      (G := G) (q := q) localActivity := by
  intro S hS
  by_cases hEmpty : S = ∅
  · simpa [hEmpty] using hzero
  · have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    by_cases hge : 2 ≤ S.card
    · calc
        visibleL1 (anovaComponent S (xopError (G := G) (q := q))) =
            visibleL1 (fun y => ∑ i : Index S, contribution S i y) := by
              rw [hexp S hS hSnonempty hge]
        _ ≤ ∑ i : Index S, visibleL1 (contribution S i) := by
              simpa using
                (visibleL1_sum_le (G := G) (q := q)
                  (A := (Finset.univ : Finset (Index S)))
                  (g := fun i => contribution S i))
        _ ≤ localActivity S.card := hactivity S hS hSnonempty hge
    · have hlt : S.card < 2 := Nat.lt_of_not_ge hge
      have hcard : S.card = 1 := by
        have hpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
        omega
      rcases Finset.card_eq_one.mp hcard with ⟨i, rfl⟩
      simpa using hsingle i

/-- Advantage endpoint for the corrected support-indexed Penrose/Ursell
expansion interface. -/
theorem xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_activity_sum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    {contribution : SupportIndexedContribution (G := G) (q := q) Index}
    {localActivity : Nat → ℝ}
    (hexp : SupportIndexedExpansionGeTwo (G := G) (q := q) Index contribution)
    (hactivity : SupportIndexedActivityBoundGeTwo (G := G) (q := q)
      Index contribution localActivity)
    (hzero : visibleL1 (anovaComponent ∅ (xopError (G := G) (q := q))) ≤
      localActivity 0)
    (hsingle : ∀ i : Fin q,
      visibleL1 (anovaComponent {i} (xopError (G := G) (q := q))) ≤
        localActivity 1)
    (hsum : (∑ S ∈ (coordinates q).powerset, localActivity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_activity_sum (G := G) (q := q) ε
    (componentActivityBound_of_supportIndexedExpansionGeTwo
      (G := G) (q := q) hexp hactivity hzero hsingle)
    hsum

/-- The pair-cluster expansion obligation left for the Penrose/Mayer stage.

The contribution family is explicit because the final connected contribution is
expected to be a Penrose/cumulant-resummed object, not necessarily the raw
connected edge product. -/
def PairClusterExpansion [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (contribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset,
    anovaComponent S (xopError (G := G) (q := q)) =
      fun y => ∑ C : PairCluster S, contribution S C y

/-- The expansion actually needed by the scalar XoP theorem after the empty and
singleton ANOVA components have been discharged.  This avoids forcing a
Penrose/cumulant construction to explain irrelevant supports of size zero or one
when the final theorem only consumes the `|S| ≥ 2` component estimates. -/
def PairClusterExpansionGeTwo [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (contribution : PairClusterContribution (G := G) (q := q)) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    anovaComponent S (xopError (G := G) (q := q)) =
      fun y => ∑ C : PairCluster S, contribution S C y

/-- Pair-cluster estimate strong enough to feed the existing ANOVA bridge. -/
def PairClusterActivityBound [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (contribution : PairClusterContribution (G := G) (q := q)) (activity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset,
    (∑ C : PairCluster S, visibleL1 (contribution S C)) ≤
      activity S.card

/-- Per-cluster charge estimate.  This is a support-indexed alternative to the
coarser cardinality-indexed activity interface, useful before the final
tree-graph summability step collapses charges to a closed-form function of
`|S|`. -/
def PairClusterChargeBound [AddGroup G] [Fintype G] [DecidableEq G]
    (contribution : PairClusterContribution (G := G) (q := q))
    (charge : (S : Finset (Fin q)) → PairCluster S → ℝ) : Prop :=
  ∀ S (C : PairCluster S), visibleL1 (contribution S C) ≤ charge S C

/-- The actual Penrose/tree-graph obligation for a contribution family.

This is intentionally separate from the raw full-atomized positive charge.  The
accepted proof must supply a contribution family already containing the
pair-Mayer/Penrose cancellations, then bound its selected tree fibers by
support-size activity. -/
def PairClusterPenroseTreeActivityBound [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G]
    (contribution : PairClusterContribution (G := G) (q := q))
    (treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ)
    (localActivity : Nat → ℝ) : Prop :=
  PairClusterExpansion (G := G) (q := q) contribution ∧
  (∀ S ∈ (coordinates q).powerset, S.Nonempty →
    (∑ C : PairCluster S, visibleL1 (contribution S C)) ≤
      ∑ T : PairTree S, treeCharge S T) ∧
  (∀ S ∈ (coordinates q).powerset, S.Nonempty →
    (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)

/-- Selected-tree fiber bounds for the actual Penrose contribution family
package the theorem-facing Penrose activity obligation.

Unlike the raw full-atomized selected-fiber charge, this statement is about
`visibleL1 (contribution S C)`, so any cancellation must already be present in
the supplied contribution family. -/
theorem pairClusterPenroseTreeActivityBound_of_selectedContributionFiberBound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (contribution S C)) ≤ treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card) :
    PairClusterPenroseTreeActivityBound (G := G) (q := q)
      contribution treeCharge localActivity := by
  refine ⟨hexp, ?_, hlocal⟩
  intro S hSpow hS
  classical
  calc
    (∑ C : PairCluster S, visibleL1 (contribution S C)) =
        ∑ T : PairTree S,
          ∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
            (fun C => pairClusterSpanningTree C hS = T),
            visibleL1 (contribution S C) := by
          rw [Finset.sum_fiberwise]
    _ ≤ ∑ T : PairTree S, treeCharge S T := by
          exact Finset.sum_le_sum (fun T _ => hfiber S hSpow hS T)

/-- Penrose activity obligation after the zero contribution of supports of size
zero and one has been separated.  This is the scalar-tail-friendly form: only
supports of size at least two need a local activity bound. -/
def PairClusterPenroseActivityBoundGeTwo [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G]
    (contribution : PairClusterContribution (G := G) (q := q))
    (localActivity : Nat → ℝ) : Prop :=
  PairClusterExpansion (G := G) (q := q) contribution ∧
  (∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (∑ C : PairCluster S, visibleL1 (contribution S C)) ≤ localActivity S.card)

/-- Ge-two Penrose activity obligation using only the expansion that the final
ANOVA tail actually needs. -/
def PairClusterPenroseActivityBoundGeTwoOnly [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G]
    (contribution : PairClusterContribution (G := G) (q := q))
    (localActivity : Nat → ℝ) : Prop :=
  PairClusterExpansionGeTwo (G := G) (q := q) contribution ∧
  (∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (∑ C : PairCluster S, visibleL1 (contribution S C)) ≤ localActivity S.card)

/-- The full expansion interface implies the ge-two-only interface. -/
theorem pairClusterPenroseActivityBoundGeTwoOnly_of_full
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ}
    (h : PairClusterPenroseActivityBoundGeTwo (G := G) (q := q) contribution localActivity) :
    PairClusterPenroseActivityBoundGeTwoOnly (G := G) (q := q) contribution localActivity := by
  rcases h with ⟨hexp, hactivity⟩
  exact ⟨fun S hS _hne _hge => hexp S hS, hactivity⟩

/-- Selected-tree fiber bounds for the actual contribution family, with only
support sizes at least two required. -/
theorem pairClusterPenroseActivityBoundGeTwo_of_selectedContributionFiberBound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (contribution S C)) ≤ treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card) :
    PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
      contribution localActivity := by
  refine ⟨hexp, ?_⟩
  intro S hSpow hS hge
  classical
  calc
    (∑ C : PairCluster S, visibleL1 (contribution S C)) =
        ∑ T : PairTree S,
          ∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
            (fun C => pairClusterSpanningTree C hS = T),
            visibleL1 (contribution S C) := by
          rw [Finset.sum_fiberwise]
    _ ≤ ∑ T : PairTree S, treeCharge S T := by
          exact Finset.sum_le_sum (fun T _ => hfiber S hSpow hS T)
    _ ≤ localActivity S.card := hlocal S hSpow hS hge

/-- Selected-tree fiber bounds for a ge-two-only contribution expansion. -/
theorem pairClusterPenroseActivityBoundGeTwoOnly_of_selectedContributionFiberBound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hexp : PairClusterExpansionGeTwo (G := G) (q := q) contribution)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (contribution S C)) ≤ treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card) :
    PairClusterPenroseActivityBoundGeTwoOnly (G := G) (q := q)
      contribution localActivity := by
  refine ⟨hexp, ?_⟩
  intro S hSpow hS hge
  classical
  calc
    (∑ C : PairCluster S, visibleL1 (contribution S C)) =
        ∑ T : PairTree S,
          ∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
            (fun C => pairClusterSpanningTree C hS = T),
            visibleL1 (contribution S C) := by
          rw [Finset.sum_fiberwise]
    _ ≤ ∑ T : PairTree S, treeCharge S T := by
          exact Finset.sum_le_sum (fun T _ => hfiber S hSpow hS T)
    _ ≤ localActivity S.card := hlocal S hSpow hS hge

/-- Mathlib tree edge count specialized to `PairTree`, stated with `Nat.card`
so no separate edge-set `Fintype` instance is needed. -/
theorem pairTree_natCard_edgeSet_add_one (S : Finset (Fin q)) (T : PairTree S) :
    Nat.card T.1.edgeSet + 1 = Nat.card S := by
  exact ((SimpleGraph.isTree_iff_connected_and_card (G := T.1)).mp T.2).2

/-- Tree edge count rewritten using the finset support cardinality. -/
theorem pairTree_natCard_edgeSet_add_one_eq_card (S : Finset (Fin q)) (T : PairTree S) :
    Nat.card T.1.edgeSet + 1 = S.card := by
  simpa using pairTree_natCard_edgeSet_add_one (q := q) S T

/-- Crude but reusable tree-count bound: every pair tree is a simple graph on
`S`, and every simple graph is encoded by a binary labeling of the complete
graph edges.  This is not the Penrose cancellation itself; it is the counting
factor needed after a genuine per-tree charge has been proved. -/
theorem pairTree_card_le_two_pow_choose (S : Finset (Fin q)) :
    Fintype.card (PairTree S) ≤ 2 ^ (S.card.choose 2) := by
  classical
  calc
    Fintype.card (PairTree S) ≤ Fintype.card (SimpleGraph S) := by
      unfold PairTree
      exact Fintype.card_subtype_le (p := fun T : SimpleGraph S => T.IsTree)
    _ ≤ Fintype.card (SimpleGraph.TopEdgeLabeling S (Fin 2)) := by
      refine Fintype.card_le_of_embedding ?_
      refine ⟨fun G => SimpleGraph.toTopEdgeLabeling G, ?_⟩
      intro G H h
      have hlabel : (SimpleGraph.toTopEdgeLabeling G).labelGraph 1 =
          (SimpleGraph.toTopEdgeLabeling H).labelGraph 1 :=
        congrArg (fun C => C.labelGraph 1) h
      calc
        G = (SimpleGraph.toTopEdgeLabeling G).labelGraph 1 :=
          (SimpleGraph.toTopEdgeLabeling_labelGraph G).symm
        _ = (SimpleGraph.toTopEdgeLabeling H).labelGraph 1 := hlabel
        _ = H := SimpleGraph.toTopEdgeLabeling_labelGraph H
    _ = 2 ^ (S.card.choose 2) := by
      rw [SimpleGraph.card_topEdgeLabeling]
      simp

/-- Uniform per-tree charge bound summed over all pair trees.  This is the
finite-sum adapter needed once the Penrose construction supplies a bound for
each selected tree fiber. -/
theorem pairTree_sum_le_two_pow_choose_mul {S : Finset (Fin q)}
    (treeCharge : PairTree S → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbound : ∀ T : PairTree S, treeCharge T ≤ b) :
    (∑ T : PairTree S, treeCharge T) ≤ (2 ^ (S.card.choose 2) : ℝ) * b := by
  calc
    (∑ T : PairTree S, treeCharge T) ≤ ∑ _T : PairTree S, b := by
      exact Finset.sum_le_sum (fun T _ => hbound T)
    _ = (Fintype.card (PairTree S) : ℝ) * b := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ (S.card.choose 2) : ℝ) * b := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast pairTree_card_le_two_pow_choose (q := q) S) hb

/-- Layer of a support-indexed pair-cluster charge at fixed support size.

This is the exact finite-sum boundary needed by the Penrose/tree-graph
summability step: after the tree inequality controls the charge on every
`k`-point support, the final analytic estimate only has to sum these layers. -/
def PairClusterChargeLayer
    (charge : (S : Finset (Fin q)) → PairCluster S → ℝ) (k : Nat) : ℝ :=
  ∑ S ∈ (coordinates q).powersetCard k, ∑ C : PairCluster S, charge S C

/-- Reindex the total support-indexed pair-cluster charge by support size.

This is a thin wrapper around Mathlib's `Finset.sum_powerset`; it is kept here
because the final Penrose obligation is naturally stated in terms of layers. -/
theorem pairClusterCharge_sum_by_card
    (charge : (S : Finset (Fin q)) → PairCluster S → ℝ) :
    (∑ S ∈ (coordinates q).powerset, ∑ C : PairCluster S, charge S C) =
      ∑ k ∈ Finset.range ((coordinates q).card + 1),
        PairClusterChargeLayer (q := q) charge k := by
  simpa [PairClusterChargeLayer] using
    (Finset.sum_powerset (s := coordinates q)
      (f := fun S : Finset (Fin q) => ∑ C : PairCluster S, charge S C))

/-- Layer of a support-indexed tree charge at fixed support size. -/
def PairTreeChargeLayer
    (treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ) (k : Nat) : ℝ :=
  ∑ S ∈ (coordinates q).powersetCard k, ∑ T : PairTree S, treeCharge S T

/-- Reindex total tree charge by support size. -/
theorem pairTreeCharge_sum_by_card
    (treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ) :
    (∑ S ∈ (coordinates q).powerset, ∑ T : PairTree S, treeCharge S T) =
      ∑ k ∈ Finset.range ((coordinates q).card + 1),
        PairTreeChargeLayer (q := q) treeCharge k := by
  simpa [PairTreeChargeLayer] using
    (Finset.sum_powerset (s := coordinates q)
      (f := fun S : Finset (Fin q) => ∑ T : PairTree S, treeCharge S T))

/-- A local support-size bound on tree charges implies the corresponding
global layer bound with the standard binomial support count. -/
theorem pairTreeChargeLayer_le_choose_mul
    (treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ) (localActivity : Nat → ℝ)
    (hlocal : ∀ S ∈ (coordinates q).powerset,
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (k : Nat) :
    PairTreeChargeLayer (q := q) treeCharge k ≤
      ((coordinates q).card.choose k : ℝ) * localActivity k := by
  unfold PairTreeChargeLayer
  calc
    (∑ S ∈ (coordinates q).powersetCard k, ∑ T : PairTree S, treeCharge S T)
        ≤ ∑ S ∈ (coordinates q).powersetCard k, localActivity S.card := by
            refine Finset.sum_le_sum ?_
            intro S hS
            exact hlocal S (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1)
    _ = ∑ S ∈ (coordinates q).powersetCard k, localActivity k := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          rw [(Finset.mem_powersetCard.mp hS).2]
    _ = ((coordinates q).card.choose k : ℝ) * localActivity k := by
          rw [Finset.sum_const, Finset.card_powersetCard]
          simp [nsmul_eq_mul]

/-- Reindex a nonempty-support local activity sum by support cardinality. -/
theorem nonemptySupportActivity_sum_by_card (localActivity : Nat → ℝ) :
    (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty), localActivity S.card) =
      ∑ k ∈ Finset.range ((coordinates q).card + 1),
        if k = 0 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k := by
  classical
  calc
    (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty), localActivity S.card)
        = ∑ S ∈ (coordinates q).powerset, if S.Nonempty then localActivity S.card else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range ((coordinates q).card + 1),
          ∑ S ∈ (coordinates q).powersetCard k, if S.Nonempty then localActivity S.card else 0 := by
          exact Finset.sum_powerset (s := coordinates q)
            (f := fun S : Finset (Fin q) => if S.Nonempty then localActivity S.card else 0)
    _ = ∑ k ∈ Finset.range ((coordinates q).card + 1),
        if k = 0 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          by_cases hk0 : k = 0
          · subst hk0
            have hzero :
                (∑ S ∈ (coordinates q).powersetCard 0,
                  if S.Nonempty then localActivity S.card else 0) = 0 := by
              exact Finset.sum_eq_zero (fun S hS => by
                have hcard : S.card = 0 := (Finset.mem_powersetCard.mp hS).2
                have hSempty : ¬ S.Nonempty := by
                  exact fun hne => (Finset.card_pos.mpr hne).ne' hcard
                simp [hSempty])
            exact hzero
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            calc
              (∑ S ∈ (coordinates q).powersetCard k,
                  if S.Nonempty then localActivity S.card else 0)
                  = ∑ S ∈ (coordinates q).powersetCard k, localActivity k := by
                    refine Finset.sum_congr rfl ?_
                    intro S hS
                    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
                    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
                    simp [hSne, hcard]
              _ = ((coordinates q).card.choose k : ℝ) * localActivity k := by
                rw [Finset.sum_const, Finset.card_powersetCard]
                simp [nsmul_eq_mul]
              _ = if k = 0 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k := by
                simp [hk0]

/-- Reindex a nonempty-support local activity sum when supports of size zero
and one have already been shown to contribute zero. -/
theorem nonemptySupportActivity_sum_by_card_ge_two (localActivity : Nat → ℝ) :
    (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      if S.card < 2 then 0 else localActivity S.card) =
      ∑ k ∈ Finset.range ((coordinates q).card + 1),
        if k < 2 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k := by
  rw [nonemptySupportActivity_sum_by_card (q := q)
    (localActivity := fun k => if k < 2 then 0 else localActivity k)]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · by_cases hk2 : k < 2
    · have hk1 : k = 1 := by omega
      simp [hk1]
    · simp [hk0, hk2]

/-- Rewrite a finite support-cardinality sum with zero terms below two as an
interval tail. -/
theorem sum_range_if_ge_two_eq_Ico (n : Nat) (f : Nat → ℝ) :
    (∑ k ∈ Finset.range (n + 1), if k < 2 then 0 else f k) =
      ∑ k ∈ Finset.Ico 2 (n + 1), f k := by
  calc
    (∑ k ∈ Finset.range (n + 1), if k < 2 then 0 else f k)
        = ∑ k ∈ Finset.range (n + 1), if ¬ k < 2 then f k else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          by_cases hk : k < 2 <;> simp [hk]
    _ = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ k < 2), f k := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.Ico 2 (n + 1), f k := by
      have hset : (Finset.range (n + 1)).filter (fun k => ¬ k < 2) =
          Finset.Ico 2 (n + 1) := by
        ext k
        simp [Finset.mem_Ico]
        omega
      rw [hset]

/-- Reindex a support activity sum restricted directly to supports of size at
least two. -/
theorem geTwoSupportActivity_sum_by_card (localActivity : Nat → ℝ) :
    (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
      localActivity S.card) =
      ∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
        ((coordinates q).card.choose k : ℝ) * localActivity k := by
  calc
    (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card), localActivity S.card)
        = ∑ S ∈ (coordinates q).powerset,
            if 2 ≤ S.card then localActivity S.card else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ S ∈ (coordinates q).powerset,
            if S.Nonempty then (if S.card < 2 then 0 else localActivity S.card) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro S _hS
          by_cases hge : 2 ≤ S.card
          · have hSne : S.Nonempty :=
              Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hge)
            have hnlt : ¬ S.card < 2 := not_lt.mpr hge
            simp [hge, hSne, hnlt]
          · have hlt : S.card < 2 := Nat.lt_of_not_ge hge
            by_cases hSne : S.Nonempty
            · simp [hge, hSne, hlt]
            · simp [hge, hSne]
    _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            if S.card < 2 then 0 else localActivity S.card := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range ((coordinates q).card + 1),
          if k < 2 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k := by
          exact nonemptySupportActivity_sum_by_card_ge_two (q := q) localActivity
    _ = ∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
          ((coordinates q).card.choose k : ℝ) * localActivity k := by
          exact sum_range_if_ge_two_eq_Ico ((coordinates q).card)
            (fun k => ((coordinates q).card.choose k : ℝ) * localActivity k)

/-- Ge-two support-indexed Penrose/Ursell endpoint with scalar summability over
the support-size tail.  Empty and singleton ANOVA components are discharged by
the already-proved XoP normalization facts. -/
theorem xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_Ico
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    {contribution : SupportIndexedContribution (G := G) (q := q) Index}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : SupportIndexedExpansionGeTwo (G := G) (q := q) Index contribution)
    (hactivity : SupportIndexedActivityBoundGeTwo (G := G) (q := q)
      Index contribution localActivity)
    (hIco : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * localActivity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε ?_
  dsimp [XoPComponentL1Bound]
  have hcomponent : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      visibleL1 (anovaComponent S (xopError (G := G) (q := q))) ≤ localActivity S.card := by
    intro S hSpow hS hge
    rw [hexp S hSpow hS hge]
    exact le_trans
      (visibleL1_sum_le (G := G) (q := q)
        (Finset.univ : Finset (Index S)) (fun i => contribution S i))
      (hactivity S hSpow hS hge)
  have hsupport :
      (∑ S ∈ (coordinates q).powerset,
          visibleL1 (anovaComponent S (xopError (G := G) (q := q)))) ≤
        ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
          localActivity S.card := by
    calc
      (∑ S ∈ (coordinates q).powerset,
          visibleL1 (anovaComponent S (xopError (G := G) (q := q)))) =
          ∑ S ∈ (coordinates q).powerset,
            if 2 ≤ S.card then
              visibleL1 (anovaComponent S (xopError (G := G) (q := q))) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S _hS
            by_cases hge : 2 ≤ S.card
            · simp [hge]
            · have hlt : S.card < 2 := Nat.lt_of_not_ge hge
              by_cases hSne : S.Nonempty
              · have hcard : S.card = 1 := by
                  have hpos : 0 < S.card := Finset.card_pos.mpr hSne
                  omega
                rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
                simp [hi,
                  ANOVA.visibleL1_anovaComponent_singleton_xopError_of_project_density_eq_one
                    (G := G) (q := q) i
                    (ANOVA.project_singleton_visibleDensityRatioReal_eq_one
                      (G := G) (q := q) hq i)]
              · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
                simp [hSempty, visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq]
      _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
            visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
            localActivity S.card := by
          refine Finset.sum_le_sum ?_
          intro S hSfilter
          have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
          have hge : 2 ≤ S.card := (Finset.mem_filter.mp hSfilter).2
          have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hge)
          exact hcomponent S hSpow hS hge
  have htail :
      (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
          localActivity S.card) ≤ (ε : ℝ) := by
    rwa [geTwoSupportActivity_sum_by_card (q := q) localActivity]
  exact le_trans hsupport htail

/-- Monotonicity of the support-size binomial tail with respect to the local
activity. -/
theorem sum_Ico_choose_mul_le_of_activity_le (n : Nat) {activity bound : Nat → ℝ}
    (h : ∀ k ∈ Finset.Ico 2 (n + 1), activity k ≤ bound k) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * activity k) ≤
      ∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * bound k := by
  refine Finset.sum_le_sum ?_
  intro k hk
  exact mul_le_mul_of_nonneg_left (h k hk) (Nat.cast_nonneg _)

/-- Scalar binomial-sum identity used by the final activity summability leaf. -/
theorem sum_range_choose_mul_pow_eq_add_pow (n : Nat) (a : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k) = (1 + a) ^ n := by
  have hpow :=
    Finset.sum_pow_mul_eq_add_pow (a := a) (b := (1 : ℝ))
      (s := (Finset.univ : Finset (Fin n)))
  have hcard :=
    Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin n)))
      (f := fun k => a ^ k)
  calc
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k)
        = ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, a ^ t.card := by
            simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcard.symm
    _ = (a + 1) ^ n := by
            simpa using hpow
    _ = (1 + a) ^ n := by rw [add_comm]

/-- Conservative scalar bound: the `k ≥ 2` binomial tail is bounded by the
full binomial sum when the activity ratio is nonnegative. -/
theorem sum_Ico_choose_mul_pow_le_add_pow (n : Nat) {a : ℝ} (ha : 0 ≤ a) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * a ^ k) ≤ (1 + a) ^ n := by
  rw [← sum_range_choose_mul_pow_eq_add_pow]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro k hk
    simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
    omega
  · intro k _hkIco _hkRange
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha k)

/-- The low-order (`k = 0, 1`) part of the binomial sum. -/
theorem sum_range_if_lt_two_choose_mul_pow (n : Nat) (a : ℝ) :
    (∑ k ∈ Finset.range (n + 1), if k < 2 then (n.choose k : ℝ) * a ^ k else 0) =
      1 + (n : ℝ) * a := by
  cases n with
  | zero => simp
  | succ n =>
      have hset : (Finset.range (n + 2)).filter (fun k => k < 2) =
          ({0, 1} : Finset Nat) := by
        ext k
        simp [Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [← Finset.sum_filter]
      rw [hset]
      simp [Nat.choose_one_right]

/-- Exact additive form of the `k ≥ 2` binomial tail. -/
theorem sum_Ico_choose_mul_pow_add_low_eq_add_pow (n : Nat) (a : ℝ) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * a ^ k) + (1 + (n : ℝ) * a) =
      (1 + a) ^ n := by
  have hsplit :
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k) =
        (∑ k ∈ Finset.range (n + 1), if k < 2 then (n.choose k : ℝ) * a ^ k else 0) +
        (∑ k ∈ Finset.range (n + 1), if k < 2 then 0 else (n.choose k : ℝ) * a ^ k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases h : k < 2 <;> simp [h]
  rw [← sum_range_if_ge_two_eq_Ico]
  rw [← sum_range_if_lt_two_choose_mul_pow n a]
  rw [add_comm]
  rw [← hsplit]
  rw [sum_range_choose_mul_pow_eq_add_pow]

/-- Subtractive form of the exact `k ≥ 2` binomial-tail identity. -/
theorem sum_Ico_choose_mul_pow_eq_add_pow_sub_low (n : Nat) (a : ℝ) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * a ^ k) =
      (1 + a) ^ n - (1 + (n : ℝ) * a) := by
  have h := sum_Ico_choose_mul_pow_add_low_eq_add_pow n a
  linarith

/-- A single binomial-tail term is bounded by the corresponding geometric term. -/
theorem choose_mul_pow_le_mul_pow (n k : Nat) {a : ℝ} (ha : 0 ≤ a) :
    (n.choose k : ℝ) * a ^ k ≤ ((n : ℝ) * a) ^ k := by
  have hchooseNat : n.choose k ≤ n ^ k := Nat.choose_le_pow n k
  have hchoose : (n.choose k : ℝ) ≤ (n ^ k : ℝ) := by
    exact_mod_cast hchooseNat
  calc
    (n.choose k : ℝ) * a ^ k ≤ (n ^ k : ℝ) * a ^ k := by
      exact mul_le_mul_of_nonneg_right hchoose (pow_nonneg ha k)
    _ = ((n : ℝ) * a) ^ k := by
      rw [mul_pow]

/-- The binomial tail is bounded by a geometric tail with ratio `n * a`. -/
theorem sum_Ico_choose_mul_pow_le_sum_Ico_mul_pow (n : Nat) {a : ℝ} (ha : 0 ≤ a) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * a ^ k) ≤
      ∑ k ∈ Finset.Ico 2 (n + 1), ((n : ℝ) * a) ^ k := by
  refine Finset.sum_le_sum ?_
  intro k _hk
  exact choose_mul_pow_le_mul_pow n k ha

/-- Geometric-tail form of the scalar binomial-tail bound.  This is the
summability shape consumed once a local Penrose activity is bounded by
`a^k` and `(q * a) < 1`. -/
theorem sum_Ico_choose_mul_pow_le_geom_tail (n : Nat) {a : ℝ}
    (ha : 0 ≤ a) (hsmall : (n : ℝ) * a < 1) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * a ^ k) ≤
      (((n : ℝ) * a) ^ 2) / (1 - (n : ℝ) * a) := by
  exact le_trans (sum_Ico_choose_mul_pow_le_sum_Ico_mul_pow n ha)
    (geom_sum_Ico_le_of_lt_one (m := 2) (n := n + 1)
      (mul_nonneg (Nat.cast_nonneg n) ha) hsmall)

/-- Birthday-scale corollary of the scalar tail: if the geometric ratio is at
most `1/2`, the `k ≥ 2` binomial tail is bounded by twice its first geometric
term. -/
theorem sum_Ico_choose_mul_pow_le_two_mul_sq (n : Nat) {a : ℝ}
    (ha : 0 ≤ a) (hsmall : (n : ℝ) * a ≤ 1 / 2) :
    (∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : ℝ) * a ^ k) ≤
      2 * (((n : ℝ) * a) ^ 2) := by
  have hlt : (n : ℝ) * a < 1 := by linarith
  refine le_trans (sum_Ico_choose_mul_pow_le_geom_tail n ha hlt) ?_
  have hden : 1 / 2 ≤ 1 - (n : ℝ) * a := by linarith
  have hsquare : 0 ≤ ((n : ℝ) * a) ^ 2 := sq_nonneg _
  calc
    ((n : ℝ) * a) ^ 2 / (1 - (n : ℝ) * a) ≤
        ((n : ℝ) * a) ^ 2 / (1 / 2) := by
          exact div_le_div_of_nonneg_left hsquare (by norm_num : (0 : ℝ) < 1 / 2) hden
    _ = 2 * (((n : ℝ) * a) ^ 2) := by ring

/-- Connected pair-cluster expansion plus cluster activity bounds imply the
existing component activity interface. -/
theorem componentActivityBound_of_pairClusterActivity [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    {contribution : PairClusterContribution (G := G) (q := q)}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcluster : PairClusterActivityBound (G := G) (q := q) contribution activity) :
    RandomSystems.Applications.XoP.ANOVA.ComponentActivityBound
      (G := G) (q := q) activity := by
  intro S hS
  rw [hexp S hS]
  have hsum :=
    visibleL1_sum_le (G := G) (q := q) (A := (Finset.univ : Finset (PairCluster S)))
      (g := fun C => contribution S C)
  exact le_trans (by simpa using hsum) (hcluster S hS)

/-- The theorem-level endpoint for the current pair-Mayer route: a connected
pair-cluster expansion plus summable activities proves the concrete
injective-input XoP advantage bound. -/
theorem xop_advantageOn_injective_of_pairClusterActivity [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (ε : NNReal) {activity : Nat → ℝ}
    {contribution : PairClusterContribution (G := G) (q := q)}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcluster : PairClusterActivityBound (G := G) (q := q) contribution activity)
    (hsum : (∑ S ∈ (coordinates q).powerset, activity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_activity_sum (G := G) (q := q) ε
    (componentActivityBound_of_pairClusterActivity (G := G) (q := q) hexp hcluster)
    hsum

/-- Pair-cluster expansion plus per-cluster charges imply the concrete ANOVA
component `L¹` bound once the total charge is summable. -/
theorem componentL1Bound_of_pairClusterExpansion_charge [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal}
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (hsum : (∑ S ∈ (coordinates q).powerset, ∑ C : PairCluster S, charge S C) ≤
      (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  dsimp [XoPComponentL1Bound]
  refine le_trans ?_ hsum
  refine Finset.sum_le_sum ?_
  intro S hS
  rw [hexp S hS]
  exact le_trans
    (visibleL1_sum_le (G := G) (q := q) (A := (Finset.univ : Finset (PairCluster S)))
      (g := fun C => contribution S C))
    (by
      simpa using Finset.sum_le_sum (fun C _ => hcharge S C))

/-- Variant of the charge endpoint that delegates the empty ANOVA component to
an explicit zero premise and estimates only nonempty supports.  This is the
right shape for the Penrose spanning-tree route because Mathlib trees are
nonempty. -/
theorem componentL1Bound_of_pairClusterExpansion_charge_nonempty
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] {ε : NNReal}
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    (hempty : visibleL1 (anovaComponent (∅ : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      ∑ C : PairCluster S, charge S C) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  dsimp [XoPComponentL1Bound]
  refine le_trans ?_ hsum
  calc
    (∑ S ∈ (coordinates q).powerset, visibleL1 (anovaComponent S (xopError (G := G) (q := q))))
        = ∑ S ∈ (coordinates q).powerset,
            if S.Nonempty then visibleL1 (anovaComponent S (xopError (G := G) (q := q))) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro S _hS
              by_cases hSne : S.Nonempty
              · simp [hSne]
              · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
                simp [hSempty, hempty]
    _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
          rw [Finset.sum_filter]
    _ ≤ ∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            ∑ C : PairCluster S, charge S C := by
          refine Finset.sum_le_sum ?_
          intro S hSfilter
          have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
          rw [hexp S hSpow]
          exact le_trans
            (visibleL1_sum_le (G := G) (q := q) (A := (Finset.univ : Finset (PairCluster S)))
              (g := fun C => contribution S C))
            (by simpa using Finset.sum_le_sum (fun C _ => hcharge S C))

/-- Layer-summed pair-cluster charges imply the concrete ANOVA component bound.

This is the form expected from the final Penrose summability argument. -/
theorem componentL1Bound_of_pairClusterExpansion_charge_layers [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal}
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (hlayers : (∑ k ∈ Finset.range ((coordinates q).card + 1),
        PairClusterChargeLayer (q := q) charge k) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  exact componentL1Bound_of_pairClusterExpansion_charge (G := G) (q := q) hexp hcharge
    (by
      rwa [pairClusterCharge_sum_by_card (q := q) charge])

/-- The charge-form pair-cluster endpoint, before cardinality-only activity
summability is extracted. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_charge [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (hsum : (∑ S ∈ (coordinates q).powerset, ∑ C : PairCluster S, charge S C) ≤
      (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε
    (componentL1Bound_of_pairClusterExpansion_charge (G := G) (q := q) hexp hcharge hsum)

/-- Charge-form pair-cluster endpoint over nonempty supports, with an explicit
empty-component-zero premise. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_charge_nonempty
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    (hempty : visibleL1 (anovaComponent (∅ : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      ∑ C : PairCluster S, charge S C) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε
    (componentL1Bound_of_pairClusterExpansion_charge_nonempty (G := G) (q := q)
      hempty hexp hcharge hsum)

/-- Layer-summed pair-cluster endpoint, matching the final Penrose/tree-graph
summability obligation. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_charge_layers
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (hlayers : (∑ k ∈ Finset.range ((coordinates q).card + 1),
        PairClusterChargeLayer (q := q) charge k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε
    (componentL1Bound_of_pairClusterExpansion_charge_layers (G := G) (q := q) hexp hcharge
      hlayers)

/-- Tree-charge handoff for the Penrose stage.

The point of this endpoint is that the difficult theorem proves `htree` without
ever summing raw connected graphs.  Once the tree charges themselves are
summable, the existing pair-cluster charge endpoint closes the security bound. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hsum : (∑ S ∈ (coordinates q).powerset, ∑ T : PairTree S, treeCharge S T) ≤
      (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_charge (G := G) (q := q) ε
    hexp hcharge
    (le_trans (Finset.sum_le_sum (fun S hS => htree S hS)) hsum)

/-- Tree-charge handoff over nonempty supports, with the empty ANOVA component
handled separately. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    (hempty : visibleL1 (anovaComponent (∅ : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      ∑ T : PairTree S, treeCharge S T) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_charge_nonempty
    (G := G) (q := q) ε hempty hexp hcharge
    (le_trans
      (Finset.sum_le_sum (fun S hS =>
        htree S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2))
      hsum)

/-- Domain-sized variant of the nonempty tree-charge endpoint.  The only extra
work is discharging the empty ANOVA component from the normalized-counting
identity `E_I R = 1`. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_of_domain
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      ∑ T : PairTree S, treeCharge S T) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty
    (G := G) (q := q) ε
    (visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq)
    hexp hcharge htree hsum

/-- Nonempty tree-charge endpoint from a local support-size activity estimate.
The summability premise is intentionally over nonempty supports; a later scalar
lemma may bound it by a binomial/geometric expression. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_of_domain
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      localActivity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_of_domain
    (G := G) (q := q) ε hq hexp hcharge htree
    (le_trans
      (Finset.sum_le_sum (fun S hS =>
        hlocal S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2))
      hsum)

/-- Nonempty local-activity endpoint with scalar summability already reindexed
by support size. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_cardSum_of_domain
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hcardSum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      if k = 0 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k) ≤
        (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_of_domain
    (G := G) (q := q) ε hq hexp hcharge htree hlocal
    (by
      rwa [nonemptySupportActivity_sum_by_card (q := q) localActivity])

/-- Endpoint from the named Penrose/tree-graph activity obligation to the
injective-input advantage bound. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseTreeActivityBound (G := G) (q := q)
        contribution treeCharge localActivity)
    (hcardSum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      if k = 0 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k) ≤
        (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  rcases hpenrose with ⟨hexp, htree, hlocal⟩
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_cardSum_of_domain
    (G := G) (q := q) ε
    (charge := fun S C => visibleL1 (contribution S C))
    hq hexp
    (fun _S _C => le_rfl)
    htree hlocal hcardSum

/-- Penrose endpoint with the scalar summability premise expressed as an
interval tail over support sizes `k ≥ 2`. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_Ico
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (hIco : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * localActivity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  rcases hpenrose with ⟨hexp, hactivity⟩
  exact xop_advantageOn_injective_of_pairClusterExpansion_charge_nonempty
    (G := G) (q := q) ε
    (charge := fun S C => visibleL1 (contribution S C))
    (visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq)
    hexp
    (fun _S _C => le_rfl)
    (by
      have hsupport :
          (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            ∑ C : PairCluster S, visibleL1 (contribution S C)) ≤
          ∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            if S.card < 2 then 0 else localActivity S.card := by
        refine Finset.sum_le_sum ?_
        intro S hSfilter
        have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
        have hS : S.Nonempty := (Finset.mem_filter.mp hSfilter).2
        by_cases hlt : S.card < 2
        · rw [pairCluster_sum_eq_zero_of_nonempty_card_lt_two hS hlt]
          simp [hlt]
        · have hge : 2 ≤ S.card := by omega
          simpa [hlt] using hactivity S hSpow hS hge
      refine le_trans hsupport ?_
      have hsum :
          (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            if S.card < 2 then 0 else localActivity S.card) =
          ∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
            ((coordinates q).card.choose k : ℝ) * localActivity k := by
        rw [nonemptySupportActivity_sum_by_card_ge_two]
        exact sum_range_if_ge_two_eq_Ico ((coordinates q).card)
          (fun k => ((coordinates q).card.choose k : ℝ) * localActivity k)
      rwa [hsum])

/-- Ge-two-only Penrose endpoint with the scalar summability premise expressed as
an interval tail.  This is the preferred endpoint for a concrete
Penrose/cumulant construction: it only requires the cluster expansion on support
sizes that survive the already-proved empty/singleton ANOVA cancellations. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseActivityGeTwoOnly_Ico
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwoOnly (G := G) (q := q)
        contribution localActivity)
    (hIco : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * localActivity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  rcases hpenrose with ⟨hexp, hactivity⟩
  refine xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε ?_
  dsimp [XoPComponentL1Bound]
  have hcomponent : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      visibleL1 (anovaComponent S (xopError (G := G) (q := q))) ≤ localActivity S.card := by
    intro S hSpow hS hge
    rw [hexp S hSpow hS hge]
    exact le_trans
      (visibleL1_sum_le (G := G) (q := q)
        (Finset.univ : Finset (PairCluster S)) (fun C => contribution S C))
      (hactivity S hSpow hS hge)
  have hsupport :
      (∑ S ∈ (coordinates q).powerset,
          visibleL1 (anovaComponent S (xopError (G := G) (q := q)))) ≤
        ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
          localActivity S.card := by
    calc
      (∑ S ∈ (coordinates q).powerset,
          visibleL1 (anovaComponent S (xopError (G := G) (q := q)))) =
          ∑ S ∈ (coordinates q).powerset,
            if 2 ≤ S.card then
              visibleL1 (anovaComponent S (xopError (G := G) (q := q))) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S _hS
            by_cases hge : 2 ≤ S.card
            · simp [hge]
            · have hlt : S.card < 2 := Nat.lt_of_not_ge hge
              by_cases hSne : S.Nonempty
              · have hcard : S.card = 1 := by
                  have hpos : 0 < S.card := Finset.card_pos.mpr hSne
                  omega
                rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
                simp [hi,
                  ANOVA.visibleL1_anovaComponent_singleton_xopError_of_project_density_eq_one
                    (G := G) (q := q) i
                    (ANOVA.project_singleton_visibleDensityRatioReal_eq_one
                      (G := G) (q := q) hq i)]
              · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
                simp [hSempty, visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq]
      _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
            visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
            localActivity S.card := by
          refine Finset.sum_le_sum ?_
          intro S hSfilter
          have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
          have hge : 2 ≤ S.card := (Finset.mem_filter.mp hSfilter).2
          have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hge)
          exact hcomponent S hSpow hS hge
  have htail :
      (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
          localActivity S.card) ≤ (ε : ℝ) := by
    rwa [geTwoSupportActivity_sum_by_card (q := q) localActivity]
  exact le_trans hsupport htail

/-- Penrose endpoint where the local activity is first bounded by a simpler
closed-form activity on the scalar tail. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_Ico_of_activity_le
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity boundActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (hactivity : ∀ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      localActivity k ≤ boundActivity k)
    (hbound : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * boundActivity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_Ico
    (G := G) (q := q) ε hq hpenrose
    (le_trans
      (sum_Ico_choose_mul_le_of_activity_le ((coordinates q).card) hactivity)
      hbound)

/-- Closed scalar endpoint for a Penrose activity bounded by a pure power
`a^k`.  Under `(q * a) ≤ 1/2`, the support-size tail is birthday-scale. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (ha : 0 ≤ a)
    (hsmall : ((coordinates q).card : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      localActivity k ≤ a ^ k)
    (hε : 2 * ((((coordinates q).card : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_Ico_of_activity_le
    (G := G) (q := q) ε hq hpenrose hactivity
    (le_trans (sum_Ico_choose_mul_pow_le_two_mul_sq ((coordinates q).card) ha hsmall) hε)

/-- Query-count version of
`xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small`, with
`(coordinates q).card` simplified to `q`. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), localActivity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small
    (G := G) (q := q) ε hq hpenrose ha
    (by simpa [coordinates] using hsmall)
    (by simpa [coordinates] using hactivity)
    (by simpa [coordinates] using hε)

/-- Direct theorem-spine endpoint from selected-tree fiber estimates for the
actual Penrose contribution family to the scalar birthday-style bound.  The
remaining mathematical leaves are exactly `hfiber` and `hactivity`. -/
theorem xop_advantageOn_injective_of_selectedContributionFiberBound_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (contribution S C)) ≤ treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), localActivity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  have hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity :=
    pairClusterPenroseActivityBoundGeTwo_of_selectedContributionFiberBound
      (G := G) (q := q) (contribution := contribution) (treeCharge := treeCharge)
      (localActivity := localActivity) hexp hfiber hlocal
  exact xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q
    (G := G) (q := q) (contribution := contribution) (localActivity := localActivity)
    (a := a) ε hq hpenrose ha hsmall hactivity hε

/-- Selected-contribution-fiber endpoint in the conventional quadratic
field-size-scaled shape.  This is the clean theorem-facing target for the
genuine Penrose/cumulant contribution family: prove expansion, selected-tree
fiber domination, and `localActivity k ≤ (C / |G|)^k`. -/
theorem xop_advantageOn_injective_of_selectedContributionFiberBound_card_scaled_quadratic
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ} {C : ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (contribution S C)) ≤ treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hC : 0 ≤ C)
    (hsmall : (q : ℝ) * (C / (Fintype.card G : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (C / (Fintype.card G : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2) := by
  have hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity :=
    pairClusterPenroseActivityBoundGeTwo_of_selectedContributionFiberBound
      (G := G) (q := q) (contribution := contribution) (treeCharge := treeCharge)
      (localActivity := localActivity) hexp hfiber hlocal
  refine xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q
    (G := G) (q := q)
    (Real.toNNReal (2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2))
    hq hpenrose (div_nonneg hC (Nat.cast_nonneg _)) hsmall hactivity ?_
  have hshape :
      2 * (((q : ℝ) * (C / (Fintype.card G : ℝ))) ^ 2) =
        2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2 := by
    ring
  rw [hshape]
  have hnonneg : 0 ≤ 2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2 := by
    positivity
  exact le_of_eq (Real.coe_toNNReal _ hnonneg).symm

/-- Support-indexed Penrose/Ursell endpoint with a pure-power local activity
bound.  This is the corrected analogue of the pair-cluster scalar endpoint:
the expansion index may encode support partitions and block products. -/
theorem xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    {contribution : SupportIndexedContribution (G := G) (q := q) Index}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : SupportIndexedExpansionGeTwo (G := G) (q := q) Index contribution)
    (hactivity : SupportIndexedActivityBoundGeTwo (G := G) (q := q)
      Index contribution localActivity)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1), localActivity k ≤ a ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * (((q : ℝ) * a) ^ 2)) := by
  refine xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_Ico
    (G := G) (q := q) (Real.toNNReal (2 * (((q : ℝ) * a) ^ 2)))
    hq hexp hactivity ?_
  refine le_trans
    (sum_Ico_choose_mul_le_of_activity_le ((coordinates q).card)
      (by simpa [coordinates] using hlocal)) ?_
  refine le_trans
    (sum_Ico_choose_mul_pow_le_two_mul_sq ((coordinates q).card) ha
      (by simpa [coordinates] using hsmall)) ?_
  have hshape :
      2 * ((((coordinates q).card : ℝ) * a) ^ 2) =
        2 * (((q : ℝ) * a) ^ 2) := by
    simp [coordinates]
  rw [hshape]
  have hnonneg : 0 ≤ 2 * (((q : ℝ) * a) ^ 2) := by positivity
  exact le_of_eq (Real.coe_toNNReal _ hnonneg).symm

/-- Conventional quadratic field-size-scaled endpoint for the corrected
support-indexed Penrose/Ursell route. -/
theorem xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_card_scaled_quadratic
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    {contribution : SupportIndexedContribution (G := G) (q := q) Index}
    {localActivity : Nat → ℝ} {C : ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : SupportIndexedExpansionGeTwo (G := G) (q := q) Index contribution)
    (hactivity : SupportIndexedActivityBoundGeTwo (G := G) (q := q)
      Index contribution localActivity)
    (hC : 0 ≤ C)
    (hsmall : (q : ℝ) * (C / (Fintype.card G : ℝ)) ≤ 1 / 2)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (C / (Fintype.card G : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2) := by
  refine le_trans
    (xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_pow_small_q
      (G := G) (q := q) (Index := Index) (contribution := contribution)
      (localActivity := localActivity) (a := C / (Fintype.card G : ℝ))
      hq hexp hactivity (div_nonneg hC (Nat.cast_nonneg _)) hsmall hlocal) ?_
  apply le_of_eq
  congr 1
  ring

/-- Concrete support-partition endpoint.  This is the theorem-facing landing
point for a Penrose/Ursell construction indexed by a partition of the ANOVA
support and one connected cluster on each block. -/
theorem xop_advantageOn_injective_of_supportPartitionClusters_card_scaled_quadratic
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {contribution : SupportIndexedContribution (G := G) (q := q)
      (SupportPartitionClusters (q := q))}
    {localActivity : Nat → ℝ} {C : ℝ}
    (hq : q ≤ Fintype.card G)
    (hexp : SupportIndexedExpansionGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q)) contribution)
    (hactivity : SupportIndexedActivityBoundGeTwo (G := G) (q := q)
      (SupportPartitionClusters (q := q)) contribution localActivity)
    (hC : 0 ≤ C)
    (hsmall : (q : ℝ) * (C / (Fintype.card G : ℝ)) ≤ 1 / 2)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (C / (Fintype.card G : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_card_scaled_quadratic
    (G := G) (q := q) (Index := SupportPartitionClusters (q := q))
    (contribution := contribution) (localActivity := localActivity) (C := C)
    hq hexp hactivity hC hsmall hlocal

/-- Query-count endpoint with the birthday-scale real bound converted directly
to an `NNReal`.  This is the clean target once Penrose supplies
`localActivity k ≤ a^k`. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q_toNNReal
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), localActivity k ≤ a ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * (((q : ℝ) * a) ^ 2)) := by
  refine xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q
    (G := G) (q := q) (Real.toNNReal (2 * (((q : ℝ) * a) ^ 2)))
    hq hpenrose ha hsmall hactivity ?_
  have hnonneg : 0 ≤ 2 * (((q : ℝ) * a) ^ 2) := by positivity
  exact le_of_eq (Real.coe_toNNReal _ hnonneg).symm

/-- Field-size-scaled version of the Penrose power-activity endpoint.  This is
the expected landing shape for a local activity estimate
`localActivity k ≤ (C / |G|)^k`. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_card_scaled
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ} {C : ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (hC : 0 ≤ C)
    (hsmall : (q : ℝ) * (C / (Fintype.card G : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (C / (Fintype.card G : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * (((q : ℝ) * (C / (Fintype.card G : ℝ))) ^ 2)) := by
  exact xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q_toNNReal
    (G := G) (q := q) hq hpenrose
    (div_nonneg hC (Nat.cast_nonneg _)) hsmall hactivity

/-- Conventional quadratic-bound shape of the field-size-scaled Penrose
endpoint. -/
theorem xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_card_scaled_quadratic
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {contribution : PairClusterContribution (G := G) (q := q)}
    {localActivity : Nat → ℝ} {C : ℝ}
    (hq : q ≤ Fintype.card G)
    (hpenrose :
      PairClusterPenroseActivityBoundGeTwo (G := G) (q := q)
        contribution localActivity)
    (hC : 0 ≤ C)
    (hsmall : (q : ℝ) * (C / (Fintype.card G : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (C / (Fintype.card G : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤
        Real.toNNReal (2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2) := by
  have hbase := xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_card_scaled
    (G := G) (q := q) hq hpenrose hC hsmall hactivity
  have hbound : Real.toNNReal (2 * (((q : ℝ) * (C / (Fintype.card G : ℝ))) ^ 2)) =
      Real.toNNReal (2 * C ^ 2 * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) ^ 2) := by
    congr 1
    ring
  simpa [hbound] using hbase

/-- Tree-charge handoff with the tree summability hypothesis expressed by
support-size layers. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_layers
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hlayers : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      PairTreeChargeLayer (q := q) treeCharge k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge (G := G) (q := q) ε
    hexp hcharge htree
    (by
      rwa [pairTreeCharge_sum_by_card (q := q) treeCharge])

/-- Tree-charge handoff with a closed-form support-size layer bound. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_layerBound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {treeActivity : Nat → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hlayer : ∀ k ∈ Finset.range ((coordinates q).card + 1),
      PairTreeChargeLayer (q := q) treeCharge k ≤ treeActivity k)
    (hsum : (∑ k ∈ Finset.range ((coordinates q).card + 1), treeActivity k) ≤
      (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_layers
    (G := G) (q := q) ε hexp hcharge htree
    (le_trans (Finset.sum_le_sum hlayer) hsum)

/-- Tree-charge endpoint from a local support-size activity estimate and the
corresponding binomial scalar sum. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_localActivity
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {contribution : PairClusterContribution (G := G) (q := q)}
    {charge : (S : Finset (Fin q)) → PairCluster S → ℝ}
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hexp : PairClusterExpansion (G := G) (q := q) contribution)
    (hcharge : PairClusterChargeBound (G := G) (q := q) contribution charge)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, charge S C) ≤ ∑ T : PairTree S, treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset,
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hsum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * localActivity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_layerBound
    (G := G) (q := q) ε hexp hcharge htree
    (fun k hk => pairTreeChargeLayer_le_choose_mul (q := q) treeCharge localActivity hlocal k)
    hsum

/-- Edge-family component estimate before connected-cluster resummation.  This
is a useful intermediate target for nonempty supports. -/
def EdgeFamilyComponentActivityBound [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (activity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty →
    (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ))) ≤ activity S.card

/-- A sharper edge-family activity target: after off-support vanishing, it
suffices to estimate edge families whose touched vertices cover the ANOVA
support. -/
def CoveringEdgeFamilyComponentActivityBound [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (activity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty →
    (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ))) ≤
        activity S.card

/-- Covering-edge activity only for supports of size at least two. -/
def CoveringEdgeFamilyComponentActivityBoundGeTwo [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (activity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ))) ≤
        activity S.card

/-- Termwise covering-edge estimates imply the covering-family activity
interface.  This is the exact bridge consumed by the valid all-edge-family
route after the component factorization has exposed the shape of each term. -/
theorem coveringEdgeFamilyActivity_of_termwise_bound [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    {budget : Finset (Fin q) → Finset (PairEdge (coordinates q)) → ℝ}
    (hterm : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        S ⊆ edgeVertices Γ →
          visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)) ≤
            budget S Γ)
    (hsum : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ), budget S Γ) ≤ activity S.card) :
    CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity := by
  intro S hSpow hS
  exact le_trans
    (Finset.sum_le_sum (fun Γ hΓfilter => by
      have hΓpow : Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset :=
        (Finset.mem_filter.mp hΓfilter).1
      have hcover : S ⊆ edgeVertices Γ := (Finset.mem_filter.mp hΓfilter).2
      exact hterm S hSpow hS Γ hΓpow hcover))
    (hsum S hSpow hS)

/-- Termwise covering-edge estimates imply the ge-two covering activity
interface. -/
theorem coveringEdgeFamilyActivityGeTwo_of_termwise_bound [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    {budget : Finset (Fin q) → Finset (PairEdge (coordinates q)) → ℝ}
    (hterm : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        S ⊆ edgeVertices Γ →
          visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)) ≤
            budget S Γ)
    (hsum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ), budget S Γ) ≤ activity S.card) :
    CoveringEdgeFamilyComponentActivityBoundGeTwo (G := G) (q := q) activity := by
  intro S hSpow hS hge
  refine le_trans ?_ (hsum S hSpow hS hge)
  refine Finset.sum_le_sum ?_
  intro Γ hΓfilter
  exact hterm S hSpow hS hge Γ
    (Finset.mem_filter.mp hΓfilter).1
    (Finset.mem_filter.mp hΓfilter).2

/-- A ge-two covering activity estimate controls the concrete XoP ANOVA
component on that same support.  This is the theorem-spine bridge needed after
empty and singleton components have already been removed. -/
theorem nonempty_componentActivity_of_coveringEdgeFamilyActivityGeTwo [AddGroup G]
    [Fintype G] [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    (hactivity : CoveringEdgeFamilyComponentActivityBoundGeTwo (G := G) (q := q) activity)
    {S : Finset (Fin q)} (hSpow : S ∈ (coordinates q).powerset)
    (hS : S.Nonempty) (hge : 2 ≤ S.card) :
    visibleL1 (anovaComponent S (xopError (G := G) (q := q))) ≤ activity S.card := by
  rw [anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty hS]
  refine le_trans
    (visibleL1_sum_le (G := G)
      ((Finset.univ : Finset (PairEdge (coordinates q))).powerset)
      (fun Γ => anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)))
    (by
      let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
      let term := fun Γ : Finset (PairEdge (coordinates q)) =>
        visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ))
      calc
        (∑ Γ ∈ A, term Γ)
            = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then term Γ else 0 := by
                refine Finset.sum_congr rfl ?_
                intro Γ hΓ
                by_cases hcover : S ⊆ edgeVertices Γ
                · simp [hcover]
                · have hzero :
                      term Γ = 0 :=
                    visibleL1_anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset
                      (G := G) (q := q) Γ hcover
                  simp [hcover, hzero]
        _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
              rw [Finset.sum_filter]
        _ ≤ activity S.card := hactivity S hSpow hS hge)

/-- Ge-two covering activity estimates imply the component `L¹` bound once
empty and singleton ANOVA components have been discharged. -/
theorem componentL1Bound_of_coveringEdgeFamilyActivityGeTwo [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal} {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hsingleton : ∀ i : Fin q,
      visibleL1 (anovaComponent ({i} : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hactivity : CoveringEdgeFamilyComponentActivityBoundGeTwo (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
      activity S.card) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  dsimp [XoPComponentL1Bound]
  refine le_trans ?_ hsum
  calc
    (∑ S ∈ (coordinates q).powerset, visibleL1 (anovaComponent S (xopError (G := G) (q := q))))
        = ∑ S ∈ (coordinates q).powerset,
            if 2 ≤ S.card then visibleL1 (anovaComponent S (xopError (G := G) (q := q))) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro S _hS
              by_cases hge : 2 ≤ S.card
              · simp [hge]
              · have hlt : S.card < 2 := Nat.lt_of_not_ge hge
                by_cases hSne : S.Nonempty
                · have hcard : S.card = 1 := by
                    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
                    omega
                  rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
                  simp [hi, hsingleton i]
                · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
                  simp [hSempty, visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq]
    _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
            visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
          rw [Finset.sum_filter]
    _ ≤ ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card), activity S.card := by
          refine Finset.sum_le_sum ?_
          intro S hSfilter
          have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
          have hge : 2 ≤ S.card := (Finset.mem_filter.mp hSfilter).2
          have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hge)
          exact nonempty_componentActivity_of_coveringEdgeFamilyActivityGeTwo
            (G := G) (q := q) hactivity hSpow hS hge

/-- Ge-two variant of `coveringEdgeFamilyActivity_of_termwise_bound`.  This is
the form used by the scalar XoP endpoint after empty and singleton ANOVA
components have been discharged. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamily_geTwo_termwiseBudget_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    {budget : Finset (Fin q) → Finset (PairEdge (coordinates q)) → ℝ}
    (hq : q ≤ Fintype.card G)
    (hterm : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        S ⊆ edgeVertices Γ →
          visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)) ≤
            budget S Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ), budget S Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε ?_
  refine componentL1Bound_of_coveringEdgeFamilyActivityGeTwo (G := G) (q := q)
    (activity := activity) hq
    (fun i => ANOVA.visibleL1_anovaComponent_singleton_xopError_of_project_density_eq_one
      (G := G) (q := q) i
      (ANOVA.project_singleton_visibleDensityRatioReal_eq_one (G := G) (q := q) hq i))
    (coveringEdgeFamilyActivityGeTwo_of_termwise_bound
      (G := G) (q := q) (activity := activity) (budget := budget) hterm hbudget)
    (by
      rw [geTwoSupportActivity_sum_by_card (q := q) activity]
      exact le_trans
        (sum_Ico_choose_mul_le_of_activity_le ((coordinates q).card)
          (by simpa [coordinates] using hactivity))
        (le_trans
          (sum_Ico_choose_mul_pow_le_two_mul_sq ((coordinates q).card) ha
            (by simpa [coordinates] using hsmall))
          (by simpa [coordinates] using hε)))

/-- Factorized termwise estimates imply the ge-two covering activity interface.
This is the direct activity-level bridge left by the component-factorization
leaf. -/
theorem coveringEdgeFamilyActivityGeTwo_of_factorized_termwise_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    {budget : Finset (Fin q) → Finset (PairEdge (coordinates q)) → ℝ}
    (hterm : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        S ⊆ edgeVertices Γ →
          visibleL1 (anovaComponent S
              (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ)) ≤
            budget S Γ)
    (hsum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ), budget S Γ) ≤ activity S.card) :
    CoveringEdgeFamilyComponentActivityBoundGeTwo (G := G) (q := q) activity := by
  refine coveringEdgeFamilyActivityGeTwo_of_termwise_bound
    (G := G) (q := q) (activity := activity) (budget := budget) ?_ hsum
  intro S hSpow hS hge Γ hΓ hcover
  rw [normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
  exact hterm S hSpow hS hge Γ hΓ hcover

/-- Component-factorized form of the ge-two covering endpoint.  This is the
current theorem-facing leaf after the finite-product/fiber factorization: prove
termwise budgets for the connected-component product expression, then reuse the
already checked covering/summability spine. -/
theorem xop_advantageOn_injective_of_factorizedCoveringEdgeFamily_geTwo_termwiseBudget_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    {budget : Finset (Fin q) → Finset (PairEdge (coordinates q)) → ℝ}
    (hq : q ≤ Fintype.card G)
    (hterm : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        S ⊆ edgeVertices Γ →
          visibleL1 (anovaComponent S
              (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ)) ≤
            budget S Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ), budget S Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_coveringEdgeFamily_geTwo_termwiseBudget_pow_small_q
    (G := G) (q := q) ε hq ?_ hbudget ha hsmall hactivity hε
  intro S hSpow hS hge Γ hΓ hcover
  rw [normalizedPairFamilyTerm_eq_componentFactorized (G := G) Γ]
  exact hterm S hSpow hS hge Γ hΓ hcover

/-- Factorized endpoint where the local leaf is an `L¹` estimate on the
factorized pair-family term itself.  The ANOVA triangle/projection-contraction
loss is explicit in the support-dependent budget. -/
theorem xop_advantageOn_injective_of_factorizedL1Budget_geTwo_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    {termBudget : Finset (PairEdge (coordinates q)) → ℝ}
    (hq : q ≤ Fintype.card G)
    (hterm : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      visibleL1 (componentFactorizedNormalizedPairFamilyTerm (G := G) Γ) ≤
        termBudget Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        (S.powerset.card : ℝ) * termBudget Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_factorizedCoveringEdgeFamily_geTwo_termwiseBudget_pow_small_q
    (G := G) (q := q) ε hq ?_ hbudget ha hsmall hactivity hε
  intro S hSpow hS hge Γ hΓ hcover
  refine le_trans
    (visibleL1_anovaComponent_componentFactorized_le (G := G) (q := q) S Γ)
    (mul_le_mul_of_nonneg_left (hterm Γ hΓ) (Nat.cast_nonneg _))

/-- Factorized endpoint from per-connected-component local `L¹` budgets.  This
is the theorem-facing handoff from the product-space averaging leaf to the
remaining rank/codimension estimates for one connected component at a time. -/
theorem xop_advantageOn_injective_of_componentLocalL1Budget_geTwo_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    {localBudget :
      (Γ : Finset (PairEdge (coordinates q))) →
        (pairFamilySupportGraph Γ).ConnectedComponent → ℝ}
    {termBudget : Finset (PairEdge (coordinates q)) → ℝ}
    (hq : q ≤ Fintype.card G)
    (hlocal : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      ∀ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        visibleL1 (pairFamilyComponentLocalSum (G := G) Γ C) ≤ localBudget Γ C)
    (hterm : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → G) : ℝ) /
          (visibleNormalizerNNReal (G := G) (q := q) : ℝ)| *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent, localBudget Γ C ≤
          termBudget Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        (S.powerset.card : ℝ) * termBudget Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_factorizedL1Budget_geTwo_pow_small_q
    (G := G) (q := q) ε hq ?_ hbudget ha hsmall hactivity hε
  intro Γ hΓ
  rw [visibleL1_componentFactorizedNormalizedPairFamilyTerm_eq_const_mul_prod_localL1
    (G := G) (q := q) Γ]
  refine le_trans ?_ (hterm Γ hΓ)
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine Finset.prod_le_prod ?_ ?_
  · intro C _hC
    exact visibleL1_nonneg (G := G) (q := q)
      (pairFamilyComponentLocalSum (G := G) Γ C)
  · intro C _hC
    exact hlocal Γ hΓ C

/-- Covering-only edge-family estimates imply the older all-edge-family
activity interface because non-covering families have zero ANOVA component. -/
theorem edgeFamilyActivity_of_coveringEdgeFamilyActivity [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity) :
    EdgeFamilyComponentActivityBound (G := G) (q := q) activity := by
  intro S hSpow hS
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let term := fun Γ : Finset (PairEdge (coordinates q)) =>
    visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ))
  calc
    (∑ Γ ∈ A, term Γ)
        = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then term Γ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro Γ hΓ
            by_cases hcover : S ⊆ edgeVertices Γ
            · simp [hcover]
            · have hzero :
                  term Γ = 0 :=
                visibleL1_anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset
                  (G := G) (q := q) Γ hcover
              simp [hcover, hzero]
    _ = ∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), term Γ := by
          rw [Finset.sum_filter]
    _ ≤ activity S.card := hactivity S hSpow hS

/-- Termwise edge-family estimates imply the component activity bound on each
nonempty support. -/
theorem nonempty_componentActivity_of_edgeFamilyActivity [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    (hactivity : EdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    {S : Finset (Fin q)} (hSpow : S ∈ (coordinates q).powerset) (hS : S.Nonempty) :
    visibleL1 (anovaComponent S (xopError (G := G) (q := q))) ≤ activity S.card := by
  rw [anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty hS]
  exact le_trans
    (visibleL1_sum_le (G := G)
      ((Finset.univ : Finset (PairEdge (coordinates q))).powerset)
      (fun Γ => anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)))
    (hactivity S hSpow hS)

/-- Edge-family activity estimates over nonempty supports imply the component
`L¹` bound.  The empty support is discharged by the already-proved centering of
`xopError`. -/
theorem componentL1Bound_of_edgeFamilyActivity_nonempty [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal} {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hactivity : EdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      activity S.card) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  dsimp [XoPComponentL1Bound]
  refine le_trans ?_ hsum
  calc
    (∑ S ∈ (coordinates q).powerset, visibleL1 (anovaComponent S (xopError (G := G) (q := q))))
        = ∑ S ∈ (coordinates q).powerset,
            if S.Nonempty then visibleL1 (anovaComponent S (xopError (G := G) (q := q))) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro S _hS
              by_cases hSne : S.Nonempty
              · simp [hSne]
              · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
                simp [hSempty, visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq]
    _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
            visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
          rw [Finset.sum_filter]
    _ ≤ ∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty), activity S.card := by
          refine Finset.sum_le_sum ?_
          intro S hSfilter
          have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
          have hS : S.Nonempty := (Finset.mem_filter.mp hSfilter).2
          exact nonempty_componentActivity_of_edgeFamilyActivity (G := G) (q := q)
            hactivity hSpow hS

/-- Covering-only edge-family activity estimates imply the component `L¹`
bound. -/
theorem componentL1Bound_of_coveringEdgeFamilyActivity [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal} {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      activity S.card) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  exact componentL1Bound_of_edgeFamilyActivity_nonempty (G := G) (q := q) hq
    (edgeFamilyActivity_of_coveringEdgeFamilyActivity (G := G) (q := q) hactivity)
    hsum

/-- Covering-only edge-family activity estimates plug into the concrete
injective-input XoP advantage endpoint. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      activity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε
    (componentL1Bound_of_coveringEdgeFamilyActivity (G := G) (q := q) hq hactivity hsum)

/-- Covering-only edge-family estimates with singleton components removed.  The
new theorem-forced leaf is the singleton vanishing premise; once it is proved,
the summability side starts at support size two. -/
theorem componentL1Bound_of_coveringEdgeFamilyActivity_ge_two
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] {ε : NNReal}
    {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hsingleton : ∀ i : Fin q,
      visibleL1 (anovaComponent ({i} : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
      activity S.card) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  dsimp [XoPComponentL1Bound]
  refine le_trans ?_ hsum
  calc
    (∑ S ∈ (coordinates q).powerset, visibleL1 (anovaComponent S (xopError (G := G) (q := q))))
        = ∑ S ∈ (coordinates q).powerset,
            if 2 ≤ S.card then visibleL1 (anovaComponent S (xopError (G := G) (q := q))) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro S _hS
              by_cases hge : 2 ≤ S.card
              · simp [hge]
              · have hlt : S.card < 2 := Nat.lt_of_not_ge hge
                by_cases hSne : S.Nonempty
                · have hcard : S.card = 1 := by
                    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
                    omega
                  rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
                  simp [hi, hsingleton i]
                · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
                  simp [hSempty, visibleL1_anovaComponent_empty_xopError (G := G) (q := q) hq]
    _ = ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
            visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
          rw [Finset.sum_filter]
    _ ≤ ∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card), activity S.card := by
          refine Finset.sum_le_sum ?_
          intro S hSfilter
          have hSpow : S ∈ (coordinates q).powerset := (Finset.mem_filter.mp hSfilter).1
          have hge : 2 ≤ S.card := (Finset.mem_filter.mp hSfilter).2
          have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hge)
          exact nonempty_componentActivity_of_edgeFamilyActivity (G := G) (q := q)
            (edgeFamilyActivity_of_coveringEdgeFamilyActivity (G := G) (q := q) hactivity)
            hSpow hS

/-- Advantage endpoint for covering-only edge-family estimates after empty and
singleton supports have been removed. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hsingleton : ∀ i : Fin q,
      visibleL1 (anovaComponent ({i} : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => 2 ≤ S.card),
      activity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_componentL1Bound (G := G) (q := q) ε
    (componentL1Bound_of_coveringEdgeFamilyActivity_ge_two (G := G) (q := q)
      hq hsingleton hactivity hsum)

/-- Cardinality-indexed form of the ge-two covering-edge endpoint. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hsingleton : ∀ i : Fin q,
      visibleL1 (anovaComponent ({i} : Finset (Fin q)) (xopError (G := G) (q := q))) = 0)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * activity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two
    (G := G) (q := q) ε hq hsingleton hactivity
    (by rwa [geTwoSupportActivity_sum_by_card (q := q) activity])

/-- Ge-two covering-edge endpoint stated with the natural singleton-density
marginal theorem as input. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum_of_singletonDensity
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hmarginal : ∀ i : Fin q,
      project ({i} : Finset (Fin q)) (visibleDensityRatioReal (G := G) (q := q)) =
        fun _ => 1)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * activity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum
    (G := G) (q := q) ε hq
    (fun i => ANOVA.visibleL1_anovaComponent_singleton_xopError_of_project_density_eq_one
      (G := G) (q := q) i (hmarginal i))
    hactivity hsum

/-- Ge-two covering-edge endpoint with the theorem-forced singleton marginal
discharged by the compatible-count translation symmetry. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum_uniformSingleton
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ}
    (hq : q ≤ Fintype.card G)
    (hactivity : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * activity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum_of_singletonDensity
    (G := G) (q := q) ε hq
    (fun i => ANOVA.project_singleton_visibleDensityRatioReal_eq_one (G := G) (q := q) hq i)
    hactivity hsum

/-- Scalar endpoint for the covering-edge route.  The hard leaf is still the
covering activity estimate; this theorem only reuses the singleton marginal and
the already-proved binomial/geometric tail. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hcover : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (ha : 0 ≤ a)
    (hsmall : ((coordinates q).card : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 ((coordinates q).card + 1), activity k ≤ a ^ k)
    (hε : 2 * ((((coordinates q).card : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum_uniformSingleton
    (G := G) (q := q) ε hq hcover
    (le_trans (sum_Ico_choose_mul_le_of_activity_le ((coordinates q).card) hactivity)
      (le_trans (sum_Ico_choose_mul_pow_le_two_mul_sq ((coordinates q).card) ha hsmall) hε))

/-- Query-count form of
`xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small`. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card G)
    (hcover : CoveringEdgeFamilyComponentActivityBound (G := G) (q := q) activity)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small
    (G := G) (q := q) ε hq hcover ha
    (by simpa [coordinates] using hsmall)
    (by simpa [coordinates] using hactivity)
    (by simpa [coordinates] using hε)

/-- Direct covering-edge endpoint from termwise budgets to the scalar
birthday-style bound.  This is currently the valid all-edge-family path while
the genuine cumulant/Penrose contribution family remains undefined. -/
theorem xop_advantageOn_injective_of_coveringEdgeFamily_termwiseBudget_pow_small_q
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] (ε : NNReal)
    {activity : Nat → ℝ} {a : ℝ}
    {budget : Finset (Fin q) → Finset (PairEdge (coordinates q)) → ℝ}
    (hq : q ≤ Fintype.card G)
    (hterm : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        S ⊆ edgeVertices Γ →
          visibleL1 (anovaComponent S (normalizedPairFamilyTerm (G := G) Γ)) ≤
            budget S Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ), budget S Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small_q
    (G := G) (q := q) ε hq
    (coveringEdgeFamilyActivity_of_termwise_bound
      (G := G) (q := q) (activity := activity) (budget := budget) hterm hbudget)
    ha hsmall hactivity hε

/-- Abstract activity assigned to a pair-Mayer cluster on `S`.

This is intentionally defined in terms of the already accepted ANOVA component:
XOP-DAG-11 through XOP-DAG-14 must prove useful upper bounds for this quantity,
not redefine the downstream security target. -/
def PairClusterActivity [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) : ℝ :=
  visibleL1 (anovaComponent S (xopError (G := G) (q := q)))

/-- XOP-DAG-11 theorem target: pair-Mayer/Penrose analysis supplies
cardinality-indexed component activities. -/
def PairMayerActivityBound [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (activity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset,
    PairClusterActivity (G := G) (q := q) S ≤ activity S.card

/-- Pair-Mayer activity bounds plug into the generic ANOVA component interface. -/
theorem componentActivityBound_of_pairMayerActivityBound [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {activity : Nat → ℝ}
    (h : PairMayerActivityBound (G := G) (q := q) activity) :
    RandomSystems.Applications.XoP.ANOVA.ComponentActivityBound
      (G := G) (q := q) activity := by
  intro S hS
  exact h S hS

end Mayer
end XoP
end Applications
end RandomSystems
