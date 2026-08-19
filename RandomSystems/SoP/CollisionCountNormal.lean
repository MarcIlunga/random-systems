/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.CollisionSteinAnalytic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite normal approximation for a uniform coloring's collision count

This module is independent of the legacy SoP model.  It studies `q`
independent uniform colors in an arbitrary finite nonempty type `G` and the
number of equal unordered coordinate pairs.  The terminal theorem supplies
the missing finite normal-MAD estimate used by the sharp SoP asymptotics.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace RandomSystems.SoP.CollisionCountNormal

open RandomSystems.SoP.CollisionStein
open RandomSystems.SoP.XORFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem uniformAverage_finset_sum_over
    {A I : Type*} [Fintype A] [Fintype I]
    (s : Finset I) (f : I → A → ℝ) :
    uniformAverage A (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, uniformAverage A (f i) := by
  unfold uniformAverage average
  rw [Finset.sum_comm, Finset.sum_div]

/-- Unordered coordinate pairs, represented in increasing order. -/
abbrev Edge (q : Nat) := {p : Fin q × Fin q // p.1 < p.2}

def edgeLeft {q : Nat} (e : Edge q) : Fin q := e.1.1
def edgeRight {q : Nat} (e : Edge q) : Fin q := e.1.2

@[simp]
theorem edgeLeft_ne_right {q : Nat} (e : Edge q) :
    edgeLeft e ≠ edgeRight e := by
  exact Fin.ne_of_lt e.2

/-- The `0/1` collision indicator of one edge. -/
def edgeIndicator (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) : ℝ :=
  if y (edgeRight e) = y (edgeLeft e) then 1 else 0

def edgeCount (q : Nat) : Nat := Fintype.card (Edge q)

def collisionCount (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℝ :=
  ∑ e : Edge q, edgeIndicator G e y

def collisionMean (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  (edgeCount q : ℝ) / (Fintype.card G : ℝ)

def centeredCollisionCount (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  collisionCount G q y - collisionMean G q

/-- Exact collision-count variance. -/
def collisionVariance (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  (edgeCount q : ℝ) * ((Fintype.card G - 1 : Nat) : ℝ) /
    (Fintype.card G : ℝ) ^ 2

def collisionSigma (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  Real.sqrt (collisionVariance G q)

def standardizedCollisionCount
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  centeredCollisionCount G q y / collisionSigma G q

/-- Twice the number of increasing coordinate pairs is `q*(q-1)`. -/
theorem edgeCount_mul_two (q : Nat) : edgeCount q * 2 = q * (q - 1) := by
  unfold edgeCount
  rw [Fintype.card_subtype]
  let ltPairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)
  let gtPairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.2 < p.1)
  change ltPairs.card * 2 = q * (q - 1)
  have hsymm : ltPairs.card = gtPairs.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simpa [ltPairs, gtPairs] using hp
    · intro p₁ _ p₂ _ h
      exact Prod.ext (by exact (Prod.mk.inj h).2) (by exact (Prod.mk.inj h).1)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simpa [ltPairs, gtPairs] using hp
  have hdisj : Disjoint ltPairs gtPairs := by
    simp only [ltPairs, gtPairs]
    rw [Finset.disjoint_filter]
    intro p _ h₁ h₂
    exact lt_asymm h₁ h₂
  have hunion : ltPairs ∪ gtPairs =
      (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [Finset.mem_union, ltPairs, gtPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Fin.ne_of_lt h
      · exact Ne.symm (Fin.ne_of_lt h)
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hoffdiag :
      ((Finset.univ : Finset (Fin q × Fin q)).filter
        (fun p => p.1 ≠ p.2)).card = q * (q - 1) := by
    rcases q with _ | n
    · simp
    · rw [show (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
          (fun p => p.1 ≠ p.2) = Finset.univ.offDiag from by
        ext p
        simp [Finset.mem_offDiag]]
      rw [Finset.offDiag_card]
      simp only [Finset.card_univ, Fintype.card_fin, Nat.succ_sub_one]
      ring_nf
      omega
  have hsum : ltPairs.card + gtPairs.card = q * (q - 1) := by
    rw [← hoffdiag, ← hunion]
    exact (Finset.card_union_of_disjoint hdisj).symm
  rw [hsymm] at hsum
  omega

@[simp]
theorem edgeCount_eq_choose (q : Nat) : edgeCount q = q.choose 2 := by
  have h := edgeCount_mul_two q
  rw [Nat.choose_two_right]
  omega

def edgeUses {q : Nat} (e : Edge q) (i : Fin q) : Prop :=
  i = edgeLeft e ∨ i = edgeRight e

def EdgeAdjacent {q : Nat} (e f : Edge q) : Prop :=
  edgeUses e (edgeLeft f) ∨ edgeUses e (edgeRight f)

theorem edgeAdjacent_refl {q : Nat} (e : Edge q) : EdgeAdjacent e e := by
  exact Or.inl (Or.inl rfl)

theorem edgeAdjacent_symm {q : Nat} {e f : Edge q} :
    EdgeAdjacent e f ↔ EdgeAdjacent f e := by
  unfold EdgeAdjacent edgeUses
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr (Or.inr h.symm)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr (Or.inr h.symm)

/-- A distinct adjacent edge leaves one endpoint of the first edge private. -/
theorem exists_private_endpoint_of_adjacent_ne
    {q : Nat} {e f : Edge q} (hef : e ≠ f) :
    ∃ i j : Fin q,
      i ≠ j ∧
      ((i = edgeLeft e ∧ j = edgeRight e) ∨
        (i = edgeRight e ∧ j = edgeLeft e)) ∧
      i ≠ edgeLeft f ∧ i ≠ edgeRight f := by
  by_cases hll : edgeLeft e = edgeLeft f
  · have hrr : edgeRight e ≠ edgeRight f := by
      intro h
      apply hef
      apply Subtype.ext
      exact Prod.ext hll h
    have hrl : edgeRight e ≠ edgeLeft f := by
      intro h
      have he := (show edgeLeft e < edgeRight e from e.2)
      rw [hll, h] at he
      exact (lt_irrefl _ he)
    exact ⟨edgeRight e, edgeLeft e, edgeLeft_ne_right e |>.symm,
      Or.inr ⟨rfl, rfl⟩, hrl, hrr⟩
  · by_cases hlr : edgeLeft e = edgeRight f
    · have hrr : edgeRight e ≠ edgeRight f := by
        intro h
        exact edgeLeft_ne_right e (hlr.trans h.symm)
      have hrl : edgeRight e ≠ edgeLeft f := by
        intro h
        have he := (show edgeLeft e < edgeRight e from e.2)
        have hf := (show edgeLeft f < edgeRight f from f.2)
        rw [hlr, h] at he
        exact lt_asymm he hf
      exact ⟨edgeRight e, edgeLeft e, edgeLeft_ne_right e |>.symm,
        Or.inr ⟨rfl, rfl⟩, hrl, hrr⟩
    · exact ⟨edgeLeft e, edgeRight e, edgeLeft_ne_right e,
        Or.inl ⟨rfl, rfl⟩, hll, hlr⟩

def localEdges {q : Nat} (e : Edge q) : Finset (Edge q) :=
  (Finset.univ : Finset (Edge q)).filter (EdgeAdjacent e)

def outsideEdges {q : Nat} (e : Edge q) : Finset (Edge q) :=
  (Finset.univ : Finset (Edge q)).filter (fun f => ¬EdgeAdjacent e f)

@[simp]
theorem mem_localEdges {q : Nat} {e f : Edge q} :
    f ∈ localEdges e ↔ EdgeAdjacent e f := by
  simp [localEdges]

@[simp]
theorem mem_outsideEdges {q : Nat} {e f : Edge q} :
    f ∈ outsideEdges e ↔ ¬EdgeAdjacent e f := by
  simp [outsideEdges]

/-! ## Removing one independent coordinate -/

/-- Split a function tape into one selected coordinate and all remaining
coordinates. -/
def removeCoordEquiv (G : Type*) {q : Nat} (i : Fin q) :
    (Fin q → G) ≃ G × ({j : Fin q // j ≠ i} → G) where
  toFun y := (y i, fun j => y j.1)
  invFun z j := if h : j = i then z.1 else z.2 ⟨j, h⟩
  left_inv y := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv z := by
    apply Prod.ext
    · simp
    · funext j
      simp [j.2]

@[simp]
theorem removeCoordEquiv_apply_left
    (G : Type*) {q : Nat} (i : Fin q)
    (a : G) (r : {j : Fin q // j ≠ i} → G) :
    (removeCoordEquiv G i).symm (a, r) i = a := by
  simp [removeCoordEquiv]

@[simp]
theorem removeCoordEquiv_apply_ne
    (G : Type*) {q : Nat} (i j : Fin q) (hji : j ≠ i)
    (a : G) (r : {j : Fin q // j ≠ i} → G) :
    (removeCoordEquiv G i).symm (a, r) j = r ⟨j, hji⟩ := by
  simp [removeCoordEquiv, hji]

/-- Averaging a centered equality indicator against a factor that ignores one
of its coordinates gives zero. -/
theorem uniformAverage_centered_eq_mul_of_removeCoord_invariant
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {i j : Fin q} (hij : i ≠ j) (F : (Fin q → G) → ℝ)
    (hF : ∀ (r : {k : Fin q // k ≠ i} → G) (a b : G),
      F ((removeCoordEquiv G i).symm (a, r)) =
        F ((removeCoordEquiv G i).symm (b, r))) :
    uniformAverage (Fin q → G) (fun y =>
      ((if y i = y j then 1 else 0 : ℝ) -
        1 / (Fintype.card G : ℝ)) * F y) = 0 := by
  unfold uniformAverage average
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  apply div_eq_zero_iff.mpr
  left
  calc
    (∑ y : Fin q → G,
        ((if y i = y j then 1 else 0 : ℝ) -
          1 / (Fintype.card G : ℝ)) * F y) =
      ∑ z : G × ({k : Fin q // k ≠ i} → G),
        ((if ((removeCoordEquiv G i).symm z) i =
              ((removeCoordEquiv G i).symm z) j then 1 else 0 : ℝ) -
          1 / (Fintype.card G : ℝ)) *
            F ((removeCoordEquiv G i).symm z) := by
      exact Fintype.sum_equiv (removeCoordEquiv G i) _ _ (fun y => by simp)
    _ = ∑ r : ({k : Fin q // k ≠ i} → G), ∑ a : G,
        ((if a = r ⟨j, hij.symm⟩ then 1 else 0 : ℝ) -
          1 / (Fintype.card G : ℝ)) *
            F ((removeCoordEquiv G i).symm (a, r)) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro a _ha
      rw [removeCoordEquiv_apply_left,
        removeCoordEquiv_apply_ne G i j hij.symm]
    _ = ∑ r : ({k : Fin q // k ≠ i} → G),
        F ((removeCoordEquiv G i).symm
          (r ⟨j, hij.symm⟩, r)) *
          (∑ a : G, ((if a = r ⟨j, hij.symm⟩ then 1 else 0 : ℝ) -
            1 / (Fintype.card G : ℝ))) := by
      apply Finset.sum_congr rfl
      intro r _hr
      calc
        (∑ a : G, ((if a = r ⟨j, hij.symm⟩ then 1 else 0 : ℝ) -
            1 / (Fintype.card G : ℝ)) *
              F ((removeCoordEquiv G i).symm (a, r))) =
            ∑ a : G, ((if a = r ⟨j, hij.symm⟩ then 1 else 0 : ℝ) -
              1 / (Fintype.card G : ℝ)) *
                F ((removeCoordEquiv G i).symm
                  (r ⟨j, hij.symm⟩, r)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [hF r a (r ⟨j, hij.symm⟩)]
        _ = _ := by rw [← Finset.sum_mul]; ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r _hr
      have hone :
          (∑ a : G, (if a = r ⟨j, hij.symm⟩ then 1 else 0 : ℝ)) = 1 := by
        simp
      rw [Finset.sum_sub_distrib, hone]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hcard]
      ring

/-! ## Normalized edge variables and local neighborhoods -/

def centeredEdge (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) : ℝ :=
  edgeIndicator G e y - 1 / (Fintype.card G : ℝ)

def normalizedEdge (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) : ℝ :=
  centeredEdge G e y / collisionSigma G q

def outsideNormalizedSum (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) : ℝ :=
  ∑ f ∈ outsideEdges e, normalizedEdge G f y

def localNormalizedSum (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) : ℝ :=
  ∑ f ∈ localEdges e, normalizedEdge G f y

def neighborEdges {q : Nat} (e : Edge q) : Finset (Edge q) :=
  (localEdges e).erase e

theorem centeredCollisionCount_eq_sum_centeredEdge
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    centeredCollisionCount G q y = ∑ e : Edge q, centeredEdge G e y := by
  unfold centeredCollisionCount collisionCount collisionMean centeredEdge edgeCount
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem standardizedCollisionCount_eq_sum_normalizedEdge
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    standardizedCollisionCount G q y = ∑ e : Edge q, normalizedEdge G e y := by
  rw [standardizedCollisionCount, centeredCollisionCount_eq_sum_centeredEdge]
  unfold normalizedEdge
  rw [Finset.sum_div]

theorem standardizedCollisionCount_split
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) :
    standardizedCollisionCount G q y =
      outsideNormalizedSum G e y + localNormalizedSum G e y := by
  rw [standardizedCollisionCount_eq_sum_normalizedEdge]
  unfold outsideNormalizedSum localNormalizedSum outsideEdges localEdges
  rw [add_comm, Finset.sum_filter_add_sum_filter_not]

theorem localNormalizedSum_eq_edge_add_neighbors
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) :
    localNormalizedSum G e y =
      normalizedEdge G e y +
        ∑ f ∈ neighborEdges e, normalizedEdge G f y := by
  unfold localNormalizedSum neighborEdges
  have he : e ∈ localEdges e := by simp [edgeAdjacent_refl]
  rw [← Finset.sum_erase_add _ _ he]
  ring

theorem edgeIndicator_removeCoord_invariant
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} {i : Fin q} {e : Edge q}
    (hiL : i ≠ edgeLeft e) (hiR : i ≠ edgeRight e)
    (r : {k : Fin q // k ≠ i} → G) (a b : G) :
    edgeIndicator G e ((removeCoordEquiv G i).symm (a, r)) =
      edgeIndicator G e ((removeCoordEquiv G i).symm (b, r)) := by
  unfold edgeIndicator
  rw [removeCoordEquiv_apply_ne G i (edgeRight e) hiR.symm,
    removeCoordEquiv_apply_ne G i (edgeLeft e) hiL.symm,
    removeCoordEquiv_apply_ne G i (edgeRight e) hiR.symm,
    removeCoordEquiv_apply_ne G i (edgeLeft e) hiL.symm]

theorem normalizedEdge_removeCoord_invariant
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} {i : Fin q} {e : Edge q}
    (hiL : i ≠ edgeLeft e) (hiR : i ≠ edgeRight e)
    (r : {k : Fin q // k ≠ i} → G) (a b : G) :
    normalizedEdge G e ((removeCoordEquiv G i).symm (a, r)) =
      normalizedEdge G e ((removeCoordEquiv G i).symm (b, r)) := by
  unfold normalizedEdge centeredEdge
  rw [edgeIndicator_removeCoord_invariant G hiL hiR r a b]

theorem outsideNormalizedSum_removeCoord_invariant
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} {e : Edge q} {i : Fin q} (hi : edgeUses e i)
    (r : {k : Fin q // k ≠ i} → G) (a b : G) :
    outsideNormalizedSum G e ((removeCoordEquiv G i).symm (a, r)) =
      outsideNormalizedSum G e ((removeCoordEquiv G i).symm (b, r)) := by
  unfold outsideNormalizedSum
  apply Finset.sum_congr rfl
  intro f hf
  have hnot : ¬EdgeAdjacent e f := mem_outsideEdges.mp hf
  have hiL : i ≠ edgeLeft f := by
    intro h
    apply hnot
    left
    simpa [h] using hi
  have hiR : i ≠ edgeRight f := by
    intro h
    apply hnot
    right
    simpa [h] using hi
  exact normalizedEdge_removeCoord_invariant G hiL hiR r a b

theorem centeredEdge_eq_centered_eq_of_endpoints
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) {i j : Fin q}
    (hends : (i = edgeLeft e ∧ j = edgeRight e) ∨
      (i = edgeRight e ∧ j = edgeLeft e))
    (y : Fin q → G) :
    centeredEdge G e y =
      (if y i = y j then 1 else 0 : ℝ) -
        1 / (Fintype.card G : ℝ) := by
  unfold centeredEdge edgeIndicator
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [eq_comm]
  · rfl

theorem uniformAverage_normalizedEdge_mul_of_endpoint_invariant
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) {i j : Fin q} (hij : i ≠ j)
    (hends : (i = edgeLeft e ∧ j = edgeRight e) ∨
      (i = edgeRight e ∧ j = edgeLeft e))
    (F : (Fin q → G) → ℝ)
    (hF : ∀ (r : {k : Fin q // k ≠ i} → G) (a b : G),
      F ((removeCoordEquiv G i).symm (a, r)) =
        F ((removeCoordEquiv G i).symm (b, r))) :
    uniformAverage (Fin q → G)
      (fun y => normalizedEdge G e y * F y) = 0 := by
  have hzero := uniformAverage_centered_eq_mul_of_removeCoord_invariant
    G hij F hF
  calc
    uniformAverage (Fin q → G)
        (fun y => normalizedEdge G e y * F y) =
      uniformAverage (Fin q → G) (fun y =>
        (1 / collisionSigma G q) *
          (((if y i = y j then 1 else 0 : ℝ) -
            1 / (Fintype.card G : ℝ)) * F y)) := by
      apply uniformAverage_congr
      intro y
      rw [← centeredEdge_eq_centered_eq_of_endpoints G e hends y]
      unfold normalizedEdge
      ring
    _ = (1 / collisionSigma G q) *
        uniformAverage (Fin q → G) (fun y =>
          ((if y i = y j then 1 else 0 : ℝ) -
            1 / (Fintype.card G : ℝ)) * F y) :=
      uniformAverage_const_mul _ _
    _ = 0 := by
      have h := congrArg (fun z : ℝ => (1 / collisionSigma G q) * z) hzero
      simpa using h

theorem uniformAverage_normalizedEdge_mul_outside_f
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) (f : ℝ → ℝ) :
    uniformAverage (Fin q → G) (fun y =>
      normalizedEdge G e y * f (outsideNormalizedSum G e y)) = 0 := by
  apply uniformAverage_normalizedEdge_mul_of_endpoint_invariant
    G e (i := edgeRight e) (j := edgeLeft e)
      (edgeLeft_ne_right e).symm (Or.inr ⟨rfl, rfl⟩)
  intro r a b
  congr 1
  exact outsideNormalizedSum_removeCoord_invariant G
    (Or.inr rfl) r a b

theorem uniformAverage_normalizedEdge_mul_neighbor_mul_outside
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hf : f ∈ neighborEdges e)
    (g : ℝ → ℝ) :
    uniformAverage (Fin q → G) (fun y =>
      normalizedEdge G e y * normalizedEdge G f y *
        g (outsideNormalizedSum G e y)) = 0 := by
  have hne : f ≠ e := Finset.ne_of_mem_erase hf
  obtain ⟨i, j, hij, hends, hiL, hiR⟩ :=
    exists_private_endpoint_of_adjacent_ne hne.symm
  rw [show (fun y : Fin q → G =>
      normalizedEdge G e y * normalizedEdge G f y *
        g (outsideNormalizedSum G e y)) =
      (fun y => normalizedEdge G e y *
        (normalizedEdge G f y * g (outsideNormalizedSum G e y))) by
    funext y
    ring]
  apply uniformAverage_normalizedEdge_mul_of_endpoint_invariant
    G e hij hends
  intro r a b
  have hfInv := normalizedEdge_removeCoord_invariant G hiL hiR r a b
  have hiUses : edgeUses e i := by
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have houtInv := outsideNormalizedSum_removeCoord_invariant G hiUses r a b
  rw [hfInv, houtInv]

theorem uniformAverage_normalizedEdge_mul_local_without_self
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) (g : ℝ → ℝ) :
    uniformAverage (Fin q → G) (fun y =>
      normalizedEdge G e y *
        (localNormalizedSum G e y - normalizedEdge G e y) *
        g (outsideNormalizedSum G e y)) = 0 := by
  have hpoint : (fun y : Fin q → G =>
      normalizedEdge G e y *
        (localNormalizedSum G e y - normalizedEdge G e y) *
        g (outsideNormalizedSum G e y)) =
      (fun y => ∑ f ∈ neighborEdges e,
        normalizedEdge G e y * normalizedEdge G f y *
          g (outsideNormalizedSum G e y)) := by
    funext y
    rw [localNormalizedSum_eq_edge_add_neighbors]
    calc
      normalizedEdge G e y *
          (normalizedEdge G e y +
              ∑ f ∈ neighborEdges e, normalizedEdge G f y -
            normalizedEdge G e y) *
          g (outsideNormalizedSum G e y) =
        (normalizedEdge G e y *
            ∑ f ∈ neighborEdges e, normalizedEdge G f y) *
          g (outsideNormalizedSum G e y) := by ring
      _ = ∑ f ∈ neighborEdges e,
          (normalizedEdge G e y * normalizedEdge G f y) *
            g (outsideNormalizedSum G e y) := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro f _hf
        ring
  rw [hpoint, uniformAverage_finset_sum_over]
  apply Finset.sum_eq_zero
  intro f hf
  exact uniformAverage_normalizedEdge_mul_neighbor_mul_outside G hf g

/-! ## Exact one-edge and two-edge moments -/

/-- Collision probability of one fixed coordinate pair. -/
def collisionProbability (G : Type*) [Fintype G] : ℝ :=
  1 / (Fintype.card G : ℝ)

theorem collisionProbability_nonneg
    (G : Type*) [Fintype G] : 0 ≤ collisionProbability G := by
  unfold collisionProbability
  positivity

theorem collisionProbability_le_one
    (G : Type*) [Fintype G] [Nonempty G] : collisionProbability G ≤ 1 := by
  unfold collisionProbability
  have hcard : (1 : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  exact (div_le_one (by positivity : (0 : ℝ) < Fintype.card G)).mpr hcard

theorem uniformAverage_centeredEdge_eq_zero
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (centeredEdge G e) = 0 := by
  have h := uniformAverage_centered_eq_mul_of_removeCoord_invariant
    G (edgeLeft_ne_right e).symm (fun _y : Fin q → G => (1 : ℝ))
      (fun _r _a _b => rfl)
  calc
    uniformAverage (Fin q → G) (centeredEdge G e) =
        uniformAverage (Fin q → G) (fun y =>
          (if y (edgeRight e) = y (edgeLeft e) then 1 else 0 : ℝ) -
            1 / (Fintype.card G : ℝ)) := by
      apply uniformAverage_congr
      intro y
      rfl
    _ = 0 := by simpa using h

theorem uniformAverage_edgeIndicator
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (edgeIndicator G e) =
      collisionProbability G := by
  have h := uniformAverage_centeredEdge_eq_zero G e
  unfold centeredEdge at h
  rw [uniformAverage_sub, uniformAverage_const] at h
  exact sub_eq_zero.mp h

theorem centeredEdge_sq
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) :
    (centeredEdge G e y) ^ 2 =
      (1 - 2 * collisionProbability G) * centeredEdge G e y +
        collisionProbability G * (1 - collisionProbability G) := by
  unfold centeredEdge edgeIndicator collisionProbability
  by_cases h : y (edgeRight e) = y (edgeLeft e)
  · simp [h]
    ring
  · simp [h]
    ring

theorem abs_centeredEdge
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) (y : Fin q → G) :
    |centeredEdge G e y| =
      (1 - 2 * collisionProbability G) * centeredEdge G e y +
        2 * collisionProbability G * (1 - collisionProbability G) := by
  let p := collisionProbability G
  have hp0 : 0 ≤ p := collisionProbability_nonneg G
  have hp1 : p ≤ 1 := collisionProbability_le_one G
  change |edgeIndicator G e y - p| =
    (1 - 2 * p) * (edgeIndicator G e y - p) + 2 * p * (1 - p)
  by_cases h : y (edgeRight e) = y (edgeLeft e)
  · rw [show edgeIndicator G e y = 1 by simp [edgeIndicator, h]]
    rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
    ring
  · rw [show edgeIndicator G e y = 0 by simp [edgeIndicator, h]]
    rw [abs_of_nonpos (sub_nonpos.mpr hp0)]
    ring

theorem uniformAverage_centeredEdge_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (fun y => (centeredEdge G e y) ^ 2) =
      collisionProbability G * (1 - collisionProbability G) := by
  calc
    uniformAverage (Fin q → G) (fun y => (centeredEdge G e y) ^ 2) =
        uniformAverage (Fin q → G) (fun y =>
          (1 - 2 * collisionProbability G) * centeredEdge G e y +
            collisionProbability G * (1 - collisionProbability G)) := by
      apply uniformAverage_congr
      exact centeredEdge_sq G e
    _ = (1 - 2 * collisionProbability G) *
          uniformAverage (Fin q → G) (centeredEdge G e) +
        collisionProbability G * (1 - collisionProbability G) := by
      rw [uniformAverage_add, uniformAverage_const_mul, uniformAverage_const]
    _ = _ := by rw [uniformAverage_centeredEdge_eq_zero G e]; ring

theorem uniformAverage_abs_centeredEdge
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (fun y => |centeredEdge G e y|) =
      2 * collisionProbability G * (1 - collisionProbability G) := by
  calc
    uniformAverage (Fin q → G) (fun y => |centeredEdge G e y|) =
        uniformAverage (Fin q → G) (fun y =>
          (1 - 2 * collisionProbability G) * centeredEdge G e y +
            2 * collisionProbability G * (1 - collisionProbability G)) := by
      apply uniformAverage_congr
      exact abs_centeredEdge G e
    _ = (1 - 2 * collisionProbability G) *
          uniformAverage (Fin q → G) (centeredEdge G e) +
        2 * collisionProbability G * (1 - collisionProbability G) := by
      rw [uniformAverage_add, uniformAverage_const_mul, uniformAverage_const]
    _ = _ := by rw [uniformAverage_centeredEdge_eq_zero G e]; ring

theorem uniformAverage_abs_centeredEdge_pow_three
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (fun y => |centeredEdge G e y| ^ 3) =
      collisionProbability G * (1 - collisionProbability G) *
        ((1 - collisionProbability G) ^ 2 + collisionProbability G ^ 2) := by
  let p := collisionProbability G
  have hp0 : 0 ≤ p := collisionProbability_nonneg G
  have hp1 : p ≤ 1 := collisionProbability_le_one G
  have hpoint (y : Fin q → G) :
      |centeredEdge G e y| ^ 3 =
        ((1 - p) ^ 3 - p ^ 3) * centeredEdge G e y +
          p * (1 - p) ^ 3 + (1 - p) * p ^ 3 := by
    change |edgeIndicator G e y - p| ^ 3 =
      ((1 - p) ^ 3 - p ^ 3) * (edgeIndicator G e y - p) +
        p * (1 - p) ^ 3 + (1 - p) * p ^ 3
    by_cases h : y (edgeRight e) = y (edgeLeft e)
    · rw [show edgeIndicator G e y = 1 by simp [edgeIndicator, h]]
      rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
      ring
    · rw [show edgeIndicator G e y = 0 by simp [edgeIndicator, h]]
      rw [abs_of_nonpos (sub_nonpos.mpr hp0)]
      ring
  calc
    uniformAverage (Fin q → G) (fun y => |centeredEdge G e y| ^ 3) =
        uniformAverage (Fin q → G) (fun y =>
          ((1 - p) ^ 3 - p ^ 3) * centeredEdge G e y +
            p * (1 - p) ^ 3 + (1 - p) * p ^ 3) := by
      apply uniformAverage_congr
      exact hpoint
    _ = ((1 - p) ^ 3 - p ^ 3) *
          uniformAverage (Fin q → G) (centeredEdge G e) +
        (p * (1 - p) ^ 3 + (1 - p) * p ^ 3) := by
      rw [uniformAverage_add, uniformAverage_add, uniformAverage_const_mul,
        uniformAverage_const, uniformAverage_const]
      ring
    _ = p * (1 - p) * ((1 - p) ^ 2 + p ^ 2) := by
      rw [uniformAverage_centeredEdge_eq_zero G e]
      ring

theorem centeredEdge_removeCoord_invariant
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} {i : Fin q} {e : Edge q}
    (hiL : i ≠ edgeLeft e) (hiR : i ≠ edgeRight e)
    (r : {k : Fin q // k ≠ i} → G) (a b : G) :
    centeredEdge G e ((removeCoordEquiv G i).symm (a, r)) =
      centeredEdge G e ((removeCoordEquiv G i).symm (b, r)) := by
  unfold centeredEdge
  rw [edgeIndicator_removeCoord_invariant G hiL hiR r a b]

/-- Distinct edge indicators are independent in the exact form needed below:
a centered first edge cancels against every function of the second. -/
theorem uniformAverage_centeredEdge_mul_edgeFunction_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hef : e ≠ f) (φ : ℝ → ℝ) :
    uniformAverage (Fin q → G) (fun y =>
      centeredEdge G e y * φ (centeredEdge G f y)) = 0 := by
  obtain ⟨i, j, hij, hends, hiL, hiR⟩ :=
    exists_private_endpoint_of_adjacent_ne hef
  have hzero := uniformAverage_centered_eq_mul_of_removeCoord_invariant
    G hij (fun y : Fin q → G => φ (centeredEdge G f y)) (by
      intro r a b
      exact congrArg φ (centeredEdge_removeCoord_invariant G hiL hiR r a b))
  calc
    uniformAverage (Fin q → G) (fun y =>
        centeredEdge G e y * φ (centeredEdge G f y)) =
      uniformAverage (Fin q → G) (fun y =>
        ((if y i = y j then 1 else 0 : ℝ) -
          collisionProbability G) * φ (centeredEdge G f y)) := by
        apply uniformAverage_congr
        intro y
        rw [centeredEdge_eq_centered_eq_of_endpoints G e hends y]
        rfl
    _ = 0 := hzero

theorem uniformAverage_centeredEdge_mul_centeredEdge_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hef : e ≠ f) :
    uniformAverage (Fin q → G) (fun y =>
      centeredEdge G e y * centeredEdge G f y) = 0 := by
  simpa using uniformAverage_centeredEdge_mul_edgeFunction_of_ne
    G hef id

/-! ## Exact variance normalization -/

theorem collisionVariance_eq_probability
    (G : Type*) [Fintype G] [Nonempty G] (q : Nat) :
    collisionVariance G q =
      (edgeCount q : ℝ) * collisionProbability G *
        (1 - collisionProbability G) := by
  have hcard : (1 : Nat) ≤ Fintype.card G := Fintype.card_pos
  unfold collisionVariance collisionProbability
  rw [Nat.cast_sub hcard]
  field_simp
  ring

theorem edgeCount_pos {q : Nat} (hq : 2 ≤ q) : 0 < edgeCount q := by
  rw [edgeCount_eq_choose]
  exact Nat.choose_pos hq

theorem collisionVariance_pos
    (G : Type*) [Fintype G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    0 < collisionVariance G q := by
  unfold collisionVariance
  have hM : 0 < (edgeCount q : ℝ) := by exact_mod_cast edgeCount_pos hq
  have hNm1 : 0 < ((Fintype.card G - 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hN
  have hN0 : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  positivity

theorem collisionSigma_pos
    (G : Type*) [Fintype G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    0 < collisionSigma G q := by
  unfold collisionSigma
  exact Real.sqrt_pos.2 (collisionVariance_pos G hq hN)

theorem collisionSigma_sq
    (G : Type*) [Fintype G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    (collisionSigma G q) ^ 2 = collisionVariance G q := by
  unfold collisionSigma
  exact Real.sq_sqrt (collisionVariance_pos G hq hN).le

theorem uniformAverage_normalizedEdge_eq_zero
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (normalizedEdge G e) = 0 := by
  unfold normalizedEdge
  rw [show (fun y : Fin q → G =>
      centeredEdge G e y / collisionSigma G q) =
    (fun y => (1 / collisionSigma G q) * centeredEdge G e y) by
      funext y
      ring]
  rw [uniformAverage_const_mul, uniformAverage_centeredEdge_eq_zero G e,
    mul_zero]

theorem uniformAverage_normalizedEdge_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) (e : Edge q) :
    uniformAverage (Fin q → G) (fun y => (normalizedEdge G e y) ^ 2) =
      1 / (edgeCount q : ℝ) := by
  have hsigma : collisionSigma G q ≠ 0 := (collisionSigma_pos G hq hN).ne'
  have hM : (edgeCount q : ℝ) ≠ 0 := by
    exact_mod_cast (edgeCount_pos hq).ne'
  have hsquare : (collisionSigma G q) ^ 2 =
      (edgeCount q : ℝ) * collisionProbability G *
        (1 - collisionProbability G) := by
    rw [collisionSigma_sq G hq hN, collisionVariance_eq_probability]
  have hpProd : collisionProbability G * (1 - collisionProbability G) ≠ 0 := by
    intro hp
    have hv := (collisionVariance_pos G hq hN).ne'
    apply hv
    rw [collisionVariance_eq_probability, mul_assoc, hp, mul_zero]
  rw [show (fun y : Fin q → G => (normalizedEdge G e y) ^ 2) =
      (fun y => (1 / (collisionSigma G q) ^ 2) *
        (centeredEdge G e y) ^ 2) by
    funext y
    unfold normalizedEdge
    field_simp [hsigma]]
  rw [uniformAverage_const_mul, uniformAverage_centeredEdge_sq G e]
  rw [hsquare]
  field_simp [hM, hsigma, hpProd]
  exact div_self hpProd

theorem uniformAverage_normalizedEdge_mul_normalizedEdge_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hef : e ≠ f) :
    uniformAverage (Fin q → G) (fun y =>
      normalizedEdge G e y * normalizedEdge G f y) = 0 := by
  rw [show (fun y : Fin q → G =>
      normalizedEdge G e y * normalizedEdge G f y) =
    (fun y => (1 / (collisionSigma G q) ^ 2) *
      (centeredEdge G e y * centeredEdge G f y)) by
      funext y
      unfold normalizedEdge
      ring]
  rw [uniformAverage_const_mul,
    uniformAverage_centeredEdge_mul_centeredEdge_of_ne G hef, mul_zero]

theorem uniformAverage_standardizedCollisionCount_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G)
      (fun y => (standardizedCollisionCount G q y) ^ 2) = 1 := by
  have hM : (edgeCount q : ℝ) ≠ 0 := by
    exact_mod_cast (edgeCount_pos hq).ne'
  rw [show (fun y : Fin q → G =>
      (standardizedCollisionCount G q y) ^ 2) =
    (fun y => ∑ e : Edge q, ∑ f : Edge q,
      normalizedEdge G e y * normalizedEdge G f y) by
      funext y
      rw [standardizedCollisionCount_eq_sum_normalizedEdge]
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]]
  calc
    uniformAverage (Fin q → G) (fun y =>
        ∑ e : Edge q, ∑ f : Edge q,
          normalizedEdge G e y * normalizedEdge G f y) =
      ∑ e : Edge q, ∑ f : Edge q,
        uniformAverage (Fin q → G) (fun y =>
          normalizedEdge G e y * normalizedEdge G f y) := by
      rw [uniformAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro e _he
      rw [uniformAverage_finset_sum]
    _ = ∑ e : Edge q, 1 / (edgeCount q : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _he
      calc
        (∑ f : Edge q, uniformAverage (Fin q → G) (fun y =>
            normalizedEdge G e y * normalizedEdge G f y)) =
            ∑ f : Edge q, if e = f then 1 / (edgeCount q : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro f _hf
          by_cases hef : e = f
          · subst f
            rw [if_pos rfl]
            simpa [pow_two] using uniformAverage_normalizedEdge_sq G hq hN e
          · rw [if_neg hef]
            exact uniformAverage_normalizedEdge_mul_normalizedEdge_of_ne G hef
        _ = 1 / (edgeCount q : ℝ) := by simp
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      change (edgeCount q : ℝ) * (1 / (edgeCount q : ℝ)) = 1
      field_simp [hM]

theorem uniformAverage_abs_le_sqrt_uniformAverage_sq
    {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    uniformAverage A (fun x => |f x|) ≤
      Real.sqrt (uniformAverage A (fun x => (f x) ^ 2)) := by
  have hs := sum_div_card_sq_le_sum_sq_div_card
    (s := (Finset.univ : Finset A)) (f := fun x => |f x|)
  have hs' :
      (uniformAverage A (fun x => |f x|)) ^ 2 ≤
        uniformAverage A (fun x => (f x) ^ 2) := by
    simpa [uniformAverage, sq_abs] using hs
  exact Real.le_sqrt_of_sq_le hs'

theorem uniformAverage_abs_standardizedCollisionCount_le_one
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G)
      (fun y => |standardizedCollisionCount G q y|) ≤ 1 := by
  calc
    uniformAverage (Fin q → G)
        (fun y => |standardizedCollisionCount G q y|) ≤
      Real.sqrt (uniformAverage (Fin q → G)
        (fun y => (standardizedCollisionCount G q y) ^ 2)) :=
      uniformAverage_abs_le_sqrt_uniformAverage_sq _
    _ = 1 := by rw [uniformAverage_standardizedCollisionCount_sq G hq hN]; norm_num

theorem sum_normalizedEdge_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G)
    (y : Fin q → G) :
    (∑ e : Edge q, (normalizedEdge G e y) ^ 2) =
      1 + ((1 - 2 * collisionProbability G) / collisionSigma G q) *
        standardizedCollisionCount G q y := by
  have hsigma : collisionSigma G q ≠ 0 := (collisionSigma_pos G hq hN).ne'
  have hM : (edgeCount q : ℝ) ≠ 0 := by
    exact_mod_cast (edgeCount_pos hq).ne'
  have hsquare : (collisionSigma G q) ^ 2 =
      (edgeCount q : ℝ) * collisionProbability G *
        (1 - collisionProbability G) := by
    rw [collisionSigma_sq G hq hN, collisionVariance_eq_probability]
  have hedge (e : Edge q) :
      (normalizedEdge G e y) ^ 2 =
        ((1 - 2 * collisionProbability G) / collisionSigma G q) *
            normalizedEdge G e y +
          1 / (edgeCount q : ℝ) := by
    unfold normalizedEdge
    rw [div_pow, centeredEdge_sq]
    field_simp [hsigma, hM]
    rw [hsquare]
    ring
  calc
    (∑ e : Edge q, (normalizedEdge G e y) ^ 2) =
        ∑ e : Edge q,
          (((1 - 2 * collisionProbability G) / collisionSigma G q) *
              normalizedEdge G e y + 1 / (edgeCount q : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact hedge e
    _ = ((1 - 2 * collisionProbability G) / collisionSigma G q) *
          (∑ e : Edge q, normalizedEdge G e y) + 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      change ((1 - 2 * collisionProbability G) / collisionSigma G q) *
          (∑ e : Edge q, normalizedEdge G e y) +
            (edgeCount q : ℝ) * (1 / (edgeCount q : ℝ)) =
        ((1 - 2 * collisionProbability G) / collisionSigma G q) *
          (∑ e : Edge q, normalizedEdge G e y) + 1
      field_simp [hM]
    _ = _ := by
      rw [← standardizedCollisionCount_eq_sum_normalizedEdge G q y]
      ring

theorem first_local_moment_le
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (fun y =>
      |1 - ∑ e : Edge q, (normalizedEdge G e y) ^ 2|) ≤
        1 / collisionSigma G q := by
  let c : ℝ :=
    (1 - 2 * collisionProbability G) / collisionSigma G q
  have hsigma : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hp0 : 0 ≤ collisionProbability G := collisionProbability_nonneg G
  have hp1 : collisionProbability G ≤ 1 := collisionProbability_le_one G
  have habsNumerator : |1 - 2 * collisionProbability G| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hc : |c| ≤ 1 / collisionSigma G q := by
    dsimp [c]
    rw [abs_div, abs_of_pos hsigma]
    exact div_le_div_of_nonneg_right habsNumerator hsigma.le
  have hpoint (y : Fin q → G) :
      |1 - ∑ e : Edge q, (normalizedEdge G e y) ^ 2| =
        |c| * |standardizedCollisionCount G q y| := by
    rw [sum_normalizedEdge_sq G hq hN]
    dsimp [c]
    rw [show 1 -
        (1 + (1 - 2 * collisionProbability G) / collisionSigma G q *
          standardizedCollisionCount G q y) =
      -((1 - 2 * collisionProbability G) / collisionSigma G q) *
          standardizedCollisionCount G q y by ring]
    rw [abs_mul, abs_neg]
  calc
    uniformAverage (Fin q → G) (fun y =>
        |1 - ∑ e : Edge q, (normalizedEdge G e y) ^ 2|) =
      |c| * uniformAverage (Fin q → G)
        (fun y => |standardizedCollisionCount G q y|) := by
      rw [show (fun y : Fin q → G =>
          |1 - ∑ e : Edge q, (normalizedEdge G e y) ^ 2|) =
        (fun y => |c| * |standardizedCollisionCount G q y|) by
          funext y
          exact hpoint y]
      exact uniformAverage_const_mul _ _
    _ ≤ (1 / collisionSigma G q) * 1 := by
      exact mul_le_mul hc
        (uniformAverage_abs_standardizedCollisionCount_le_one G hq hN)
        (by
          unfold uniformAverage average
          positivity)
        (one_div_nonneg.mpr hsigma.le)
    _ = 1 / collisionSigma G q := by ring

/-! ## Linear size of an edge neighborhood -/

def edgesWithLeft {q : Nat} (i : Fin q) : Finset (Edge q) :=
  (Finset.univ : Finset (Edge q)).filter (fun e => edgeLeft e = i)

def edgesWithRight {q : Nat} (i : Fin q) : Finset (Edge q) :=
  (Finset.univ : Finset (Edge q)).filter (fun e => edgeRight e = i)

theorem card_edgesWithLeft_le {q : Nat} (i : Fin q) :
    (edgesWithLeft i).card ≤ q := by
  have hinj : Set.InjOn (@edgeRight q) (edgesWithLeft i : Set (Edge q)) := by
    intro e he f hf hright
    have heLeft : edgeLeft e = i := by simpa [edgesWithLeft] using he
    have hfLeft : edgeLeft f = i := by simpa [edgesWithLeft] using hf
    apply Subtype.ext
    exact Prod.ext (heLeft.trans hfLeft.symm) hright
  calc
    (edgesWithLeft i).card =
        ((edgesWithLeft i).image (@edgeRight q)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = q := by simp

theorem card_edgesWithRight_le {q : Nat} (i : Fin q) :
    (edgesWithRight i).card ≤ q := by
  have hinj : Set.InjOn (@edgeLeft q) (edgesWithRight i : Set (Edge q)) := by
    intro e he f hf hleft
    have heRight : edgeRight e = i := by simpa [edgesWithRight] using he
    have hfRight : edgeRight f = i := by simpa [edgesWithRight] using hf
    apply Subtype.ext
    exact Prod.ext hleft (heRight.trans hfRight.symm)
  calc
    (edgesWithRight i).card =
        ((edgesWithRight i).image (@edgeLeft q)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = q := by simp

def localEdgeCover {q : Nat} (e : Edge q) : Finset (Edge q) :=
  edgesWithLeft (edgeLeft e) ∪
    edgesWithLeft (edgeRight e) ∪
      edgesWithRight (edgeLeft e) ∪
        edgesWithRight (edgeRight e)

theorem localEdges_subset_localEdgeCover {q : Nat} (e : Edge q) :
    localEdges e ⊆ localEdgeCover e := by
  intro f hf
  have hadj := mem_localEdges.mp hf
  simp only [localEdgeCover, edgesWithLeft, edgesWithRight,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold EdgeAdjacent edgeUses at hadj
  rcases hadj with (h | h)
  · rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
  · rcases h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem card_localEdges_le_four_mul {q : Nat} (e : Edge q) :
    (localEdges e).card ≤ 4 * q := by
  have hsub := Finset.card_le_card (localEdges_subset_localEdgeCover e)
  have h1 := card_edgesWithLeft_le (edgeLeft e)
  have h2 := card_edgesWithLeft_le (edgeRight e)
  have h3 := card_edgesWithRight_le (edgeLeft e)
  have h4 := card_edgesWithRight_le (edgeRight e)
  have hu1 := Finset.card_union_le
    (edgesWithLeft (edgeLeft e)) (edgesWithLeft (edgeRight e))
  have hu2 := Finset.card_union_le
    (edgesWithLeft (edgeLeft e) ∪ edgesWithLeft (edgeRight e))
    (edgesWithRight (edgeLeft e))
  have hu3 := Finset.card_union_le
    ((edgesWithLeft (edgeLeft e) ∪ edgesWithLeft (edgeRight e)) ∪
      edgesWithRight (edgeLeft e))
    (edgesWithRight (edgeRight e))
  unfold localEdgeCover at hsub
  omega

theorem card_neighborEdges_le_four_mul {q : Nat} (e : Edge q) :
    (neighborEdges e).card ≤ 4 * q := by
  exact Finset.card_erase_le.trans
    (card_localEdges_le_four_mul e)

/-! ## Three-edge geometry -/

/-- One endpoint of the first edge occurs in neither of the other two. -/
def HasPrivateEndpoint {q : Nat} (e f g : Edge q) : Prop :=
  ∃ i : Fin q, edgeUses e i ∧ ¬ edgeUses f i ∧ ¬ edgeUses g i

/-- Three edges form a closed triangle when none of them has a private
endpoint.  For three distinct simple edges this is exactly the ordinary
three-cycle condition.  This formulation makes the cancellation alternative
definitionally transparent. -/
def ClosedEdgeTriangle {q : Nat} (e f g : Edge q) : Prop :=
  ¬ HasPrivateEndpoint e f g ∧
    ¬ HasPrivateEndpoint f e g ∧
      ¬ HasPrivateEndpoint g e f

theorem edge_eq_of_uses_two
    {q : Nat} {e f : Edge q} {i j : Fin q} (hij : i ≠ j)
    (hei : edgeUses e i) (hej : edgeUses e j)
    (hfi : edgeUses f i) (hfj : edgeUses f j) : e = f := by
  unfold edgeUses edgeLeft edgeRight at hei hej hfi hfj
  rcases hei with hei | hei <;>
    rcases hej with hej | hej <;>
      rcases hfi with hfi | hfi <;>
        rcases hfj with hfj | hfj
  all_goals
    apply Subtype.ext
    apply Prod.ext <;> omega

theorem uses_third_of_not_private
    {q : Nat} {e f g : Edge q} {i : Fin q}
    (h : ¬ HasPrivateEndpoint e f g)
    (hei : edgeUses e i) (hfi : ¬ edgeUses f i) : edgeUses g i := by
  by_contra hgi
  exact h ⟨i, hei, hfi, hgi⟩

theorem closedEdgeTriangle_adjacent
    {q : Nat} {e f g : Edge q}
    (hg : ClosedEdgeTriangle e f g) : EdgeAdjacent e f := by
  by_contra hnot
  have hnotSymm : ¬ EdgeAdjacent f e := by
    exact (edgeAdjacent_symm (e := f) (f := e)).not.mpr hnot
  have hnotEL : ¬ edgeUses f (edgeLeft e) := (not_or.mp hnotSymm).1
  have hnotER : ¬ edgeUses f (edgeRight e) := (not_or.mp hnotSymm).2
  have hgEL : edgeUses g (edgeLeft e) :=
    uses_third_of_not_private hg.1 (Or.inl rfl) hnotEL
  have hgER : edgeUses g (edgeRight e) :=
    uses_third_of_not_private hg.1 (Or.inr rfl) hnotER
  have hge : e = g := edge_eq_of_uses_two (edgeLeft_ne_right e)
    (Or.inl rfl) (Or.inr rfl) hgEL hgER
  have hnotFL : ¬ edgeUses e (edgeLeft f) := (not_or.mp hnot).1
  apply hg.2.1
  refine ⟨edgeLeft f, Or.inl rfl, hnotFL, ?_⟩
  simpa [← hge] using hnotFL

/-- For fixed distinct first and second edges there is at most one closed
triangle completion. -/
theorem closedEdgeTriangle_right_unique
    {q : Nat} {e f g h : Edge q} (hef : e ≠ f)
    (hg : ClosedEdgeTriangle e f g)
    (hh : ClosedEdgeTriangle e f h) : g = h := by
  obtain ⟨i, _j, _hij, hendsE, hiFL, hiFR⟩ :=
    exists_private_endpoint_of_adjacent_ne hef
  obtain ⟨k, _l, _hkl, hendsF, hkEL, hkER⟩ :=
    exists_private_endpoint_of_adjacent_ne hef.symm
  have hei : edgeUses e i := by
    rcases hendsE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hfk : edgeUses f k := by
    rcases hendsF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hfi : ¬ edgeUses f i := by
    intro h
    rcases h with h | h
    · exact hiFL h
    · exact hiFR h
  have hek : ¬ edgeUses e k := by
    intro h
    rcases h with h | h
    · exact hkEL h
    · exact hkER h
  have hik : i ≠ k := by
    intro hik
    apply hfi
    simpa [hik] using hfk
  have hgi : edgeUses g i := uses_third_of_not_private hg.1 hei hfi
  have hgk : edgeUses g k := uses_third_of_not_private hg.2.1 hfk hek
  have hhi : edgeUses h i := uses_third_of_not_private hh.1 hei hfi
  have hhk : edgeUses h k := uses_third_of_not_private hh.2.1 hfk hek
  exact edge_eq_of_uses_two hik hgi hgk hhi hhk

/-- If the first two edges collide in a closed triangle, the third edge also
collides. -/
theorem closedEdgeTriangle_collision
    {G : Type*} [DecidableEq G] {q : Nat} {e f g : Edge q}
    (hef : e ≠ f) (hg : ClosedEdgeTriangle e f g) (y : Fin q → G)
    (heq : y (edgeRight e) = y (edgeLeft e))
    (hfeq : y (edgeRight f) = y (edgeLeft f)) :
    y (edgeRight g) = y (edgeLeft g) := by
  have hadj := closedEdgeTriangle_adjacent hg
  obtain ⟨i, j, _hij, hendsE, hiFL, hiFR⟩ :=
    exists_private_endpoint_of_adjacent_ne hef
  obtain ⟨k, l, _hkl, hendsF, hkEL, hkER⟩ :=
    exists_private_endpoint_of_adjacent_ne hef.symm
  have hei : edgeUses e i := by
    rcases hendsE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hej : edgeUses e j := by
    rcases hendsE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hfk : edgeUses f k := by
    rcases hendsF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hfl : edgeUses f l := by
    rcases hendsF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hfi : ¬ edgeUses f i := by
    intro h
    rcases h with h | h
    · exact hiFL h
    · exact hiFR h
  have hek : ¬ edgeUses e k := by
    intro h
    rcases h with h | h
    · exact hkEL h
    · exact hkER h
  have hlUsesE : edgeUses e l := by
    unfold EdgeAdjacent at hadj
    rcases hendsF with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · rcases hadj with hadj | hadj
      · exact False.elim (hek (by simpa [hk] using hadj))
      · simpa [hl] using hadj
    · rcases hadj with hadj | hadj
      · simpa [hl] using hadj
      · exact False.elim (hek (by simpa [hk] using hadj))
  have hli : l ≠ i := by
    intro hli
    apply hfi
    simpa [hli] using hfl
  have hlj : l = j := by
    unfold edgeUses at hlUsesE hei hej
    rcases hlUsesE with hl | hl <;>
      rcases hei with hi | hi <;>
        rcases hej with hj | hj <;> omega
  have hgi : edgeUses g i := uses_third_of_not_private hg.1 hei hfi
  have hgk : edgeUses g k := uses_third_of_not_private hg.2.1 hfk hek
  have hik : i ≠ k := by
    intro hik
    apply hfi
    simpa [hik] using hfk
  have hyij : y i = y j := by
    rcases hendsE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact heq.symm
    · exact heq
  have hykl : y k = y l := by
    rcases hendsF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hfeq.symm
    · exact hfeq
  have hyik : y i = y k := by
    rw [hyij, ← hlj, ← hykl]
  unfold edgeUses at hgi hgk
  rcases hgi with hgi | hgi <;> rcases hgk with hgk | hgk
  · exact False.elim (hik (hgi.trans hgk.symm))
  · simpa [hgi, hgk] using hyik.symm
  · simpa [hgi, hgk] using hyik
  · exact False.elim (hik (hgi.trans hgk.symm))

/-! ## Three-edge centered moments -/

theorem uniformAverage_centeredEdge_mul_of_endpoint_invariant
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) {i j : Fin q} (hij : i ≠ j)
    (hends : (i = edgeLeft e ∧ j = edgeRight e) ∨
      (i = edgeRight e ∧ j = edgeLeft e))
    (F : (Fin q → G) → ℝ)
    (hF : ∀ (r : {k : Fin q // k ≠ i} → G) (a b : G),
      F ((removeCoordEquiv G i).symm (a, r)) =
        F ((removeCoordEquiv G i).symm (b, r))) :
    uniformAverage (Fin q → G) (fun y => centeredEdge G e y * F y) = 0 := by
  have hzero := uniformAverage_centered_eq_mul_of_removeCoord_invariant
    G hij F hF
  calc
    uniformAverage (Fin q → G) (fun y => centeredEdge G e y * F y) =
      uniformAverage (Fin q → G) (fun y =>
        ((if y i = y j then 1 else 0 : ℝ) -
          collisionProbability G) * F y) := by
        apply uniformAverage_congr
        intro y
        rw [centeredEdge_eq_centered_eq_of_endpoints G e hends y]
        rfl
    _ = 0 := hzero

theorem uniformAverage_centeredEdge_triple_eq_zero_of_private
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f g : Edge q} (hprivate : HasPrivateEndpoint e f g) :
    uniformAverage (Fin q → G) (fun y =>
      centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) = 0 := by
  obtain ⟨i, hiE, hiF, hiG⟩ := hprivate
  rw [show (fun y : Fin q → G =>
      centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) =
    (fun y => centeredEdge G e y *
      (centeredEdge G f y * centeredEdge G g y)) by
        funext y
        ring]
  rcases hiE with hiE | hiE
  · subst i
    apply uniformAverage_centeredEdge_mul_of_endpoint_invariant
      G e (i := edgeLeft e) (j := edgeRight e) (edgeLeft_ne_right e)
        (Or.inl ⟨rfl, rfl⟩)
    intro r a b
    have hfL : edgeLeft e ≠ edgeLeft f := fun h => hiF (Or.inl h)
    have hfR : edgeLeft e ≠ edgeRight f := fun h => hiF (Or.inr h)
    have hgL : edgeLeft e ≠ edgeLeft g := fun h => hiG (Or.inl h)
    have hgR : edgeLeft e ≠ edgeRight g := fun h => hiG (Or.inr h)
    rw [centeredEdge_removeCoord_invariant G hfL hfR r a b,
      centeredEdge_removeCoord_invariant G hgL hgR r a b]
  · subst i
    apply uniformAverage_centeredEdge_mul_of_endpoint_invariant
      G e (i := edgeRight e) (j := edgeLeft e) (edgeLeft_ne_right e).symm
        (Or.inr ⟨rfl, rfl⟩)
    intro r a b
    have hfL : edgeRight e ≠ edgeLeft f := fun h => hiF (Or.inl h)
    have hfR : edgeRight e ≠ edgeRight f := fun h => hiF (Or.inr h)
    have hgL : edgeRight e ≠ edgeLeft g := fun h => hiG (Or.inl h)
    have hgR : edgeRight e ≠ edgeRight g := fun h => hiG (Or.inr h)
    rw [centeredEdge_removeCoord_invariant G hfL hfR r a b,
      centeredEdge_removeCoord_invariant G hgL hgR r a b]

theorem uniformAverage_centeredEdge_triple_eq_zero_of_not_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f g : Edge q} (hnot : ¬ ClosedEdgeTriangle e f g) :
    uniformAverage (Fin q → G) (fun y =>
      centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) = 0 := by
  by_cases he : HasPrivateEndpoint e f g
  · exact uniformAverage_centeredEdge_triple_eq_zero_of_private G he
  by_cases hf : HasPrivateEndpoint f e g
  · rw [show (fun y : Fin q → G =>
        centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) =
      (fun y => centeredEdge G f y * centeredEdge G e y * centeredEdge G g y) by
        funext y
        ring]
    exact uniformAverage_centeredEdge_triple_eq_zero_of_private G hf
  have hg : HasPrivateEndpoint g e f := by
    by_contra hg
    exact hnot ⟨he, hf, hg⟩
  rw [show (fun y : Fin q → G =>
        centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) =
      (fun y => centeredEdge G g y * centeredEdge G e y * centeredEdge G f y) by
        funext y
        ring]
  exact uniformAverage_centeredEdge_triple_eq_zero_of_private G hg

theorem uniformAverage_edgeIndicator_mul_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hef : e ≠ f) :
    uniformAverage (Fin q → G) (fun y =>
      edgeIndicator G e y * edgeIndicator G f y) =
        collisionProbability G ^ 2 := by
  let p := collisionProbability G
  have hpoint (y : Fin q → G) :
      edgeIndicator G e y * edgeIndicator G f y =
        centeredEdge G e y * centeredEdge G f y +
          p * centeredEdge G e y + p * centeredEdge G f y + p ^ 2 := by
    unfold centeredEdge
    dsimp [p, collisionProbability]
    ring
  rw [show (fun y : Fin q → G =>
      edgeIndicator G e y * edgeIndicator G f y) =
    (fun y => centeredEdge G e y * centeredEdge G f y +
      p * centeredEdge G e y + p * centeredEdge G f y + p ^ 2) by
      funext y
      exact hpoint y]
  simp only [uniformAverage_add, uniformAverage_const_mul, uniformAverage_const]
  rw [uniformAverage_centeredEdge_mul_centeredEdge_of_ne G hef,
    uniformAverage_centeredEdge_eq_zero G e,
    uniformAverage_centeredEdge_eq_zero G f]
  dsimp [p]
  ring

theorem edgeIndicator_triple_eq_pair_of_closed
    (G : Type*) [DecidableEq G] {q : Nat} {e f g : Edge q}
    (hef : e ≠ f) (hclosed : ClosedEdgeTriangle e f g) (y : Fin q → G) :
    edgeIndicator G e y * edgeIndicator G f y * edgeIndicator G g y =
      edgeIndicator G e y * edgeIndicator G f y := by
  by_cases he : y (edgeRight e) = y (edgeLeft e)
  · by_cases hf : y (edgeRight f) = y (edgeLeft f)
    · have hg := closedEdgeTriangle_collision hef hclosed y he hf
      simp [edgeIndicator, he, hf, hg]
    · simp [edgeIndicator, he, hf]
  · simp [edgeIndicator, he]

theorem uniformAverage_centeredEdge_triple_of_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f g : Edge q}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hclosed : ClosedEdgeTriangle e f g) :
    uniformAverage (Fin q → G) (fun y =>
      centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) =
      collisionProbability G ^ 2 * (1 - collisionProbability G) := by
  let p := collisionProbability G
  have htripleIndicator :
      uniformAverage (Fin q → G) (fun y =>
        edgeIndicator G e y * edgeIndicator G f y * edgeIndicator G g y) =
        p ^ 2 := by
    rw [show (fun y : Fin q → G =>
        edgeIndicator G e y * edgeIndicator G f y * edgeIndicator G g y) =
      (fun y => edgeIndicator G e y * edgeIndicator G f y) by
        funext y
        exact edgeIndicator_triple_eq_pair_of_closed G hef hclosed y]
    exact uniformAverage_edgeIndicator_mul_of_ne G hef
  have hpoint (y : Fin q → G) :
      centeredEdge G e y * centeredEdge G f y * centeredEdge G g y =
        edgeIndicator G e y * edgeIndicator G f y * edgeIndicator G g y -
          p * (edgeIndicator G e y * edgeIndicator G f y) -
          p * (edgeIndicator G e y * edgeIndicator G g y) -
          p * (edgeIndicator G f y * edgeIndicator G g y) +
          p ^ 2 * edgeIndicator G e y +
          p ^ 2 * edgeIndicator G f y +
          p ^ 2 * edgeIndicator G g y - p ^ 3 := by
    unfold centeredEdge
    dsimp [p, collisionProbability]
    ring
  rw [show (fun y : Fin q → G =>
      centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) =
    (fun y => edgeIndicator G e y * edgeIndicator G f y * edgeIndicator G g y -
      p * (edgeIndicator G e y * edgeIndicator G f y) -
      p * (edgeIndicator G e y * edgeIndicator G g y) -
      p * (edgeIndicator G f y * edgeIndicator G g y) +
      p ^ 2 * edgeIndicator G e y + p ^ 2 * edgeIndicator G f y +
      p ^ 2 * edgeIndicator G g y - p ^ 3) by
        funext y
        exact hpoint y]
  simp only [uniformAverage_sub, uniformAverage_add,
    uniformAverage_const_mul, uniformAverage_const]
  rw [htripleIndicator,
    uniformAverage_edgeIndicator_mul_of_ne G hef,
    uniformAverage_edgeIndicator_mul_of_ne G heg,
    uniformAverage_edgeIndicator_mul_of_ne G hfg,
    uniformAverage_edgeIndicator G e,
    uniformAverage_edgeIndicator G f,
    uniformAverage_edgeIndicator G g]
  dsimp [p]
  ring

theorem uniformAverage_abs_centeredEdge_mul_two_of_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f g : Edge q}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hclosed : ClosedEdgeTriangle e f g) :
    uniformAverage (Fin q → G) (fun y =>
      |centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y) =
      (1 - 2 * collisionProbability G) *
        collisionProbability G ^ 2 * (1 - collisionProbability G) := by
  let p := collisionProbability G
  have hpoint (y : Fin q → G) :
      |centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y =
        (1 - 2 * p) *
            (centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) +
          (2 * p * (1 - p)) *
            (centeredEdge G f y * centeredEdge G g y) := by
    rw [abs_centeredEdge]
    dsimp [p]
    ring
  rw [show (fun y : Fin q → G =>
      |centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y) =
    (fun y => (1 - 2 * p) *
        (centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) +
      (2 * p * (1 - p)) *
        (centeredEdge G f y * centeredEdge G g y)) by
      funext y
      exact hpoint y]
  rw [uniformAverage_add, uniformAverage_const_mul, uniformAverage_const_mul,
    uniformAverage_centeredEdge_triple_of_closed G hef heg hfg hclosed,
    uniformAverage_centeredEdge_mul_centeredEdge_of_ne G hfg]
  dsimp [p]
  ring

theorem uniformAverage_abs_centeredEdge_mul_two_of_not_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f g : Edge q} (hfg : f ≠ g)
    (hnot : ¬ ClosedEdgeTriangle e f g) :
    uniformAverage (Fin q → G) (fun y =>
      |centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y) = 0 := by
  let p := collisionProbability G
  have hpoint (y : Fin q → G) :
      |centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y =
        (1 - 2 * p) *
            (centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) +
          (2 * p * (1 - p)) *
            (centeredEdge G f y * centeredEdge G g y) := by
    rw [abs_centeredEdge]
    dsimp [p]
    ring
  rw [show (fun y : Fin q → G =>
      |centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y) =
    (fun y => (1 - 2 * p) *
        (centeredEdge G e y * centeredEdge G f y * centeredEdge G g y) +
      (2 * p * (1 - p)) *
        (centeredEdge G f y * centeredEdge G g y)) by
      funext y
      exact hpoint y]
  rw [uniformAverage_add, uniformAverage_const_mul, uniformAverage_const_mul,
    uniformAverage_centeredEdge_triple_eq_zero_of_not_closed G hnot,
    uniformAverage_centeredEdge_mul_centeredEdge_of_ne G hfg]
  ring

theorem uniformAverage_abs_normalizedEdge_mul_two_of_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G)
    {e f g : Edge q} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hclosed : ClosedEdgeTriangle e f g) :
    uniformAverage (Fin q → G) (fun y =>
      |normalizedEdge G e y| * normalizedEdge G f y * normalizedEdge G g y) =
      (1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
        (1 - collisionProbability G) / (collisionSigma G q) ^ 3 := by
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  rw [show (fun y : Fin q → G =>
      |normalizedEdge G e y| * normalizedEdge G f y * normalizedEdge G g y) =
    (fun y => (1 / (collisionSigma G q) ^ 3) *
      (|centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y)) by
        funext y
        unfold normalizedEdge
        rw [abs_div, abs_of_pos hs]
        field_simp [hs.ne']]
  rw [uniformAverage_const_mul,
    uniformAverage_abs_centeredEdge_mul_two_of_closed G hef heg hfg hclosed]
  ring

theorem uniformAverage_abs_normalizedEdge_mul_two_of_not_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f g : Edge q} (hfg : f ≠ g)
    (hnot : ¬ ClosedEdgeTriangle e f g) :
    uniformAverage (Fin q → G) (fun y =>
      |normalizedEdge G e y| * normalizedEdge G f y * normalizedEdge G g y) = 0 := by
  rw [show (fun y : Fin q → G =>
      |normalizedEdge G e y| * normalizedEdge G f y * normalizedEdge G g y) =
    (fun y => (1 / (|collisionSigma G q| * (collisionSigma G q) ^ 2)) *
      (|centeredEdge G e y| * centeredEdge G f y * centeredEdge G g y)) by
        funext y
        unfold normalizedEdge
        rw [abs_div]
        ring]
  rw [uniformAverage_const_mul,
    uniformAverage_abs_centeredEdge_mul_two_of_not_closed G hfg hnot,
    mul_zero]

theorem uniformAverage_abs_normalizedEdge_mul_self_mul_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e g : Edge q} (heg : e ≠ g) :
    uniformAverage (Fin q → G) (fun y =>
      |normalizedEdge G e y| * normalizedEdge G e y * normalizedEdge G g y) = 0 := by
  have hzero := uniformAverage_centeredEdge_mul_edgeFunction_of_ne
    G heg.symm (fun z => |z| * z)
  rw [show (fun y : Fin q → G =>
      |normalizedEdge G e y| * normalizedEdge G e y * normalizedEdge G g y) =
    (fun y => (1 / (|collisionSigma G q| * (collisionSigma G q) ^ 2)) *
      (centeredEdge G g y *
        (|centeredEdge G e y| * centeredEdge G e y))) by
        funext y
        unfold normalizedEdge
        rw [abs_div]
        ring]
  rw [uniformAverage_const_mul, hzero, mul_zero]

/-- Ordered pairs of distinct neighboring edges which close a triangle with
the fixed edge. -/
def closedTrianglePairs {q : Nat} (e : Edge q) : Finset (Edge q × Edge q) :=
  ((neighborEdges e).product (neighborEdges e)).filter
    (fun fg => fg.1 ≠ fg.2 ∧ ClosedEdgeTriangle e fg.1 fg.2)

theorem card_closedTrianglePairs_le {q : Nat} (e : Edge q) :
    (closedTrianglePairs e).card ≤ (neighborEdges e).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro fg hfg
    have hp := (Finset.mem_filter.mp hfg).1
    exact (Finset.mem_product.mp hp).1
  · intro a ha b hb hab
    apply Prod.ext
    · exact hab
    · have haMem := Finset.mem_filter.mp ha
      have hbMem := Finset.mem_filter.mp hb
      have hae : e ≠ a.1 := by
        exact (Finset.ne_of_mem_erase (Finset.mem_product.mp haMem.1).1).symm
      have htriA := haMem.2.2
      have htriB : ClosedEdgeTriangle e a.1 b.2 := by
        simpa [hab] using hbMem.2.2
      exact closedEdgeTriangle_right_unique hae htriA htriB

theorem card_closedTrianglePairs_le_four_mul {q : Nat} (e : Edge q) :
    (closedTrianglePairs e).card ≤ 4 * q :=
  (card_closedTrianglePairs_le e).trans (card_neighborEdges_le_four_mul e)

/-! ## The squared-variable neighborhood moment -/

theorem uniformAverage_centeredEdge_sq_mul_abs_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hef : e ≠ f) :
    uniformAverage (Fin q → G) (fun y =>
      (centeredEdge G e y) ^ 2 * |centeredEdge G f y|) =
        2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 := by
  let p := collisionProbability G
  have hpoint (y : Fin q → G) :
      (centeredEdge G e y) ^ 2 * |centeredEdge G f y| =
        (1 - 2 * p) *
            (centeredEdge G e y * |centeredEdge G f y|) +
          (p * (1 - p)) * |centeredEdge G f y| := by
    rw [centeredEdge_sq]
    dsimp [p]
    ring
  calc
    uniformAverage (Fin q → G) (fun y =>
        (centeredEdge G e y) ^ 2 * |centeredEdge G f y|) =
      uniformAverage (Fin q → G) (fun y =>
        (1 - 2 * p) *
            (centeredEdge G e y * |centeredEdge G f y|) +
          (p * (1 - p)) * |centeredEdge G f y|) := by
      apply uniformAverage_congr
      exact hpoint
    _ = (1 - 2 * p) * uniformAverage (Fin q → G) (fun y =>
          centeredEdge G e y * |centeredEdge G f y|) +
        (p * (1 - p)) * uniformAverage (Fin q → G) (fun y =>
          |centeredEdge G f y|) := by
      rw [uniformAverage_add, uniformAverage_const_mul,
        uniformAverage_const_mul]
    _ = 2 * (p * (1 - p)) ^ 2 := by
      rw [uniformAverage_centeredEdge_mul_edgeFunction_of_ne G hef abs,
        uniformAverage_abs_centeredEdge G f]
      dsimp [p]
      ring

theorem uniformAverage_abs_normalizedEdge_pow_three_le
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) (e : Edge q) :
    uniformAverage (Fin q → G) (fun y => |normalizedEdge G e y| ^ 3) ≤
      1 / ((edgeCount q : ℝ) * collisionSigma G q) := by
  let p := collisionProbability G
  let s := collisionSigma G q
  have hs : 0 < s := collisionSigma_pos G hq hN
  have hs' : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hM : 0 < (edgeCount q : ℝ) := by
    exact_mod_cast edgeCount_pos hq
  have hp0 : 0 ≤ p := collisionProbability_nonneg G
  have hp1 : p ≤ 1 := collisionProbability_le_one G
  have hb : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hshape : (1 - p) ^ 2 + p ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hsquare : s ^ 2 = (edgeCount q : ℝ) * p * (1 - p) := by
    dsimp [s, p]
    rw [collisionSigma_sq G hq hN, collisionVariance_eq_probability]
  have hb0 : p * (1 - p) ≠ 0 := by
    intro hzero
    rw [mul_assoc, hzero, mul_zero] at hsquare
    nlinarith [sq_pos_of_pos hs]
  have hexact :
      uniformAverage (Fin q → G) (fun y => |normalizedEdge G e y| ^ 3) =
        p * (1 - p) * ((1 - p) ^ 2 + p ^ 2) / s ^ 3 := by
    have hraw :
        uniformAverage (Fin q → G) (fun y => |normalizedEdge G e y| ^ 3) =
          collisionProbability G * (1 - collisionProbability G) *
              ((1 - collisionProbability G) ^ 2 + collisionProbability G ^ 2) /
            (collisionSigma G q) ^ 3 := by
      rw [show (fun y : Fin q → G => |normalizedEdge G e y| ^ 3) =
        (fun y => (1 / (collisionSigma G q) ^ 3) *
          |centeredEdge G e y| ^ 3) by
          funext y
          unfold normalizedEdge
          rw [abs_div, abs_of_pos hs']
          field_simp [hs'.ne']]
      rw [uniformAverage_const_mul,
        uniformAverage_abs_centeredEdge_pow_three G e]
      ring
    simpa only [p, s] using hraw
  rw [hexact]
  calc
    p * (1 - p) * ((1 - p) ^ 2 + p ^ 2) / s ^ 3 ≤
        p * (1 - p) / s ^ 3 := by
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ s ^ 3)
      exact mul_le_of_le_one_right hb hshape
    _ = 1 / ((edgeCount q : ℝ) * s) := by
      have hs0 : s ≠ 0 := hs.ne'
      have hM0 : (edgeCount q : ℝ) ≠ 0 := hM.ne'
      rw [show s ^ 3 = s ^ 2 * s by ring, hsquare]
      field_simp [hs0, hM0, hb0]
      exact div_self hb0

theorem uniformAverage_normalizedEdge_sq_mul_abs_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G)
    {e f : Edge q} (hef : e ≠ f) :
    uniformAverage (Fin q → G) (fun y =>
      (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|) =
      2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
        (collisionSigma G q) ^ 3 := by
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  rw [show (fun y : Fin q → G =>
      (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|) =
    (fun y => (1 / (collisionSigma G q) ^ 3) *
      ((centeredEdge G e y) ^ 2 * |centeredEdge G f y|)) by
      funext y
      unfold normalizedEdge
      rw [abs_div, abs_of_pos hs]
      field_simp [hs.ne']]
  rw [uniformAverage_const_mul,
    uniformAverage_centeredEdge_sq_mul_abs_of_ne G hef]
  ring

theorem abs_localNormalizedSum_le_sum_abs
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) :
    |localNormalizedSum G e y| ≤
      ∑ f ∈ localEdges e, |normalizedEdge G f y| := by
  unfold localNormalizedSum
  exact Finset.abs_sum_le_sum_abs _ _

theorem second_local_moment_le_raw
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (fun y =>
      ∑ e : Edge q, (normalizedEdge G e y) ^ 2 *
        |localNormalizedSum G e y|) ≤
      (edgeCount q : ℝ) *
        (1 / ((edgeCount q : ℝ) * collisionSigma G q) +
          ((4 * q : Nat) : ℝ) *
            (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
              (collisionSigma G q) ^ 3)) := by
  let pairMoment : ℝ :=
    2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
      (collisionSigma G q) ^ 3
  have hsigma : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hpairNonneg : 0 ≤ pairMoment := by
    dsimp [pairMoment]
    exact div_nonneg (by positivity) (by positivity)
  have hpoint (y : Fin q → G) :
      (∑ e : Edge q, (normalizedEdge G e y) ^ 2 *
          |localNormalizedSum G e y|) ≤
        ∑ e : Edge q, ∑ f ∈ localEdges e,
          (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y| := by
    apply Finset.sum_le_sum
    intro e _he
    calc
      (normalizedEdge G e y) ^ 2 * |localNormalizedSum G e y| ≤
          (normalizedEdge G e y) ^ 2 *
            (∑ f ∈ localEdges e, |normalizedEdge G f y|) :=
        mul_le_mul_of_nonneg_left (abs_localNormalizedSum_le_sum_abs G e y)
          (sq_nonneg _)
      _ = ∑ f ∈ localEdges e,
          (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y| := by
        rw [Finset.mul_sum]
  calc
    uniformAverage (Fin q → G) (fun y =>
        ∑ e : Edge q, (normalizedEdge G e y) ^ 2 *
          |localNormalizedSum G e y|) ≤
      uniformAverage (Fin q → G) (fun y =>
        ∑ e : Edge q, ∑ f ∈ localEdges e,
          (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|) :=
      uniformAverage_mono hpoint
    _ = ∑ e : Edge q, ∑ f ∈ localEdges e,
        uniformAverage (Fin q → G) (fun y =>
          (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|) := by
      rw [uniformAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro e _he
      rw [uniformAverage_finset_sum_over]
    _ ≤ ∑ _e : Edge q,
        (1 / ((edgeCount q : ℝ) * collisionSigma G q) +
          ((4 * q : Nat) : ℝ) * pairMoment) := by
      apply Finset.sum_le_sum
      intro e _he
      have heLocal : e ∈ localEdges e := by simp [edgeAdjacent_refl]
      have hsplit :
          (∑ f ∈ localEdges e,
              uniformAverage (Fin q → G) (fun y =>
                (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|)) =
            uniformAverage (Fin q → G) (fun y =>
                (normalizedEdge G e y) ^ 2 * |normalizedEdge G e y|) +
              ∑ f ∈ neighborEdges e,
                uniformAverage (Fin q → G) (fun y =>
                  (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|) := by
        unfold neighborEdges
        rw [← Finset.sum_erase_add _ _ heLocal]
        ring
      rw [hsplit]
      have hself :
          uniformAverage (Fin q → G) (fun y =>
              (normalizedEdge G e y) ^ 2 * |normalizedEdge G e y|) ≤
            1 / ((edgeCount q : ℝ) * collisionSigma G q) := by
        calc
          uniformAverage (Fin q → G) (fun y =>
              (normalizedEdge G e y) ^ 2 * |normalizedEdge G e y|) =
            uniformAverage (Fin q → G) (fun y =>
              |normalizedEdge G e y| ^ 3) := by
              apply uniformAverage_congr
              intro y
              rw [← sq_abs]
              ring
          _ ≤ _ := uniformAverage_abs_normalizedEdge_pow_three_le G hq hN e
      have hneighbors :
          (∑ f ∈ neighborEdges e,
              uniformAverage (Fin q → G) (fun y =>
                (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|)) ≤
            ((4 * q : Nat) : ℝ) * pairMoment := by
        have hterms :
            (∑ f ∈ neighborEdges e,
                uniformAverage (Fin q → G) (fun y =>
                  (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|)) =
              ((neighborEdges e).card : ℝ) * pairMoment := by
          calc
            (∑ f ∈ neighborEdges e,
                uniformAverage (Fin q → G) (fun y =>
                  (normalizedEdge G e y) ^ 2 * |normalizedEdge G f y|)) =
              ∑ _f ∈ neighborEdges e, pairMoment := by
                apply Finset.sum_congr rfl
                intro f hf
                have hne : e ≠ f := by
                  exact (Finset.ne_of_mem_erase hf).symm
                exact uniformAverage_normalizedEdge_sq_mul_abs_of_ne
                  G hq hN hne
            _ = ((neighborEdges e).card : ℝ) * pairMoment := by
              simp
        rw [hterms]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_neighborEdges_le_four_mul e) hpairNonneg
      linarith
    _ = (edgeCount q : ℝ) *
        (1 / ((edgeCount q : ℝ) * collisionSigma G q) +
          ((4 * q : Nat) : ℝ) *
            (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
              (collisionSigma G q) ^ 3)) := by
      dsimp [pairMoment]
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      rfl

theorem second_local_moment_le
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (fun y =>
      ∑ e : Edge q, (normalizedEdge G e y) ^ 2 *
        |localNormalizedSum G e y|) ≤
      1 / collisionSigma G q +
        ((8 * q : Nat) : ℝ) * collisionProbability G *
          (1 - collisionProbability G) / collisionSigma G q := by
  have hraw := second_local_moment_le_raw G hq hN
  refine hraw.trans_eq ?_
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hM : 0 < (edgeCount q : ℝ) := by
    exact_mod_cast edgeCount_pos hq
  have hsquare : (collisionSigma G q) ^ 2 =
      (edgeCount q : ℝ) * collisionProbability G *
        (1 - collisionProbability G) := by
    rw [collisionSigma_sq G hq hN, collisionVariance_eq_probability]
  field_simp [hs.ne', hM.ne']
  rw [hsquare]
  push_cast
  ring

/-! ## The Taylor-remainder neighborhood moment -/

def thirdMomentEnvelope {q : Nat} (e f g : Edge q)
    (self pair tri : ℝ) : ℝ :=
  (if f = e ∧ g = e then self else 0) +
    (if f = g ∧ f ≠ e then pair else 0) +
      (if f ≠ g ∧ f ≠ e ∧ g ≠ e ∧ ClosedEdgeTriangle e f g
        then tri else 0)

theorem sum_thirdMomentEnvelope
    {q : Nat} (e : Edge q) (self pair tri : ℝ) :
    (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
      thirdMomentEnvelope e f g self pair tri) =
      self + ((neighborEdges e).card : ℝ) * pair +
        ((closedTrianglePairs e).card : ℝ) * tri := by
  have he : e ∈ localEdges e := by simp [edgeAdjacent_refl]
  have hself :
      (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        if f = e ∧ g = e then self else 0) = self := by
    calc
      (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
          if f = e ∧ g = e then self else 0) =
        ∑ f ∈ localEdges e, if f = e then self else 0 := by
          apply Finset.sum_congr rfl
          intro f _hf
          by_cases hfe : f = e
          · subst f
            simp [he]
          · simp [hfe]
      _ = self := by simp [he]
  have hpair :
      (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        if f = g ∧ f ≠ e then pair else 0) =
        ((neighborEdges e).card : ℝ) * pair := by
    calc
      (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
          if f = g ∧ f ≠ e then pair else 0) =
        ∑ f ∈ localEdges e, if f ≠ e then pair else 0 := by
          apply Finset.sum_congr rfl
          intro f hf
          by_cases hfe : f = e
          · simp [hfe]
          · simp [hfe, hf]
      _ = ∑ f ∈ (localEdges e).filter (fun f => f ≠ e), pair := by
        rw [Finset.sum_filter]
      _ = ((neighborEdges e).card : ℝ) * pair := by
        rw [Finset.filter_ne']
        simp [neighborEdges]
  have htri :
      (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        if f ≠ g ∧ f ≠ e ∧ g ≠ e ∧ ClosedEdgeTriangle e f g
          then tri else 0) =
        ((closedTrianglePairs e).card : ℝ) * tri := by
    have hset :
        ((localEdges e).product (localEdges e)).filter (fun fg =>
          fg.1 ≠ fg.2 ∧ fg.1 ≠ e ∧ fg.2 ≠ e ∧
            ClosedEdgeTriangle e fg.1 fg.2) = closedTrianglePairs e := by
      ext fg
      simp [closedTrianglePairs, neighborEdges, and_assoc, and_left_comm,
        and_comm]
    calc
      (∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
          if f ≠ g ∧ f ≠ e ∧ g ≠ e ∧ ClosedEdgeTriangle e f g
            then tri else 0) =
        ∑ fg ∈ (localEdges e).product (localEdges e),
          if fg.1 ≠ fg.2 ∧ fg.1 ≠ e ∧ fg.2 ≠ e ∧
              ClosedEdgeTriangle e fg.1 fg.2 then tri else 0 := by
            exact (Finset.sum_product (localEdges e) (localEdges e)
              (fun fg : Edge q × Edge q =>
                if fg.1 ≠ fg.2 ∧ fg.1 ≠ e ∧ fg.2 ≠ e ∧
                  ClosedEdgeTriangle e fg.1 fg.2 then tri else (0 : ℝ))).symm
      _ = ∑ fg ∈ ((localEdges e).product (localEdges e)).filter (fun fg =>
          fg.1 ≠ fg.2 ∧ fg.1 ≠ e ∧ fg.2 ≠ e ∧
            ClosedEdgeTriangle e fg.1 fg.2), tri := by
            rw [Finset.sum_filter]
      _ = ((closedTrianglePairs e).card : ℝ) * tri := by
        rw [hset]
        simp
  unfold thirdMomentEnvelope
  simp_rw [Finset.sum_add_distrib]
  rw [hself, hpair, htri]

def thirdEdgeMoment (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e f g : Edge q) : ℝ :=
  uniformAverage (Fin q → G) (fun y =>
    |normalizedEdge G e y| * normalizedEdge G f y * normalizedEdge G g y)

theorem thirdEdgeMoment_le_envelope
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G)
    (e f g : Edge q) :
    thirdEdgeMoment G e f g ≤
      thirdMomentEnvelope e f g
        (1 / ((edgeCount q : ℝ) * collisionSigma G q))
        (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
          (collisionSigma G q) ^ 3)
        ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
          (1 - collisionProbability G) / (collisionSigma G q) ^ 3) := by
  by_cases hfg : f = g
  · subst g
    by_cases hfe : f = e
    · subst f
      have henv : thirdMomentEnvelope e e e
          (1 / ((edgeCount q : ℝ) * collisionSigma G q))
          (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
            collisionSigma G q ^ 3)
          ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
            (1 - collisionProbability G) / collisionSigma G q ^ 3) =
          1 / ((edgeCount q : ℝ) * collisionSigma G q) := by
        simp [thirdMomentEnvelope]
      rw [henv]
      unfold thirdEdgeMoment
      calc
        uniformAverage (Fin q → G) (fun y =>
            |normalizedEdge G e y| * normalizedEdge G e y *
              normalizedEdge G e y) =
          uniformAverage (Fin q → G) (fun y =>
            |normalizedEdge G e y| ^ 3) := by
              apply uniformAverage_congr
              intro y
              calc
                |normalizedEdge G e y| * normalizedEdge G e y *
                    normalizedEdge G e y =
                  |normalizedEdge G e y| * (normalizedEdge G e y) ^ 2 := by ring
                _ = |normalizedEdge G e y| * |normalizedEdge G e y| ^ 2 := by
                  rw [sq_abs]
                _ = |normalizedEdge G e y| ^ 3 := by ring
        _ ≤ _ := uniformAverage_abs_normalizedEdge_pow_three_le G hq hN e
    · have henv : thirdMomentEnvelope e f f
          (1 / ((edgeCount q : ℝ) * collisionSigma G q))
          (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
            collisionSigma G q ^ 3)
          ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
            (1 - collisionProbability G) / collisionSigma G q ^ 3) =
          2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
            collisionSigma G q ^ 3 := by
        simp [thirdMomentEnvelope, hfe]
      rw [henv]
      unfold thirdEdgeMoment
      have hm := uniformAverage_normalizedEdge_sq_mul_abs_of_ne G hq hN hfe
      rw [← hm]
      exact (uniformAverage_congr (fun y => by ring)).le
  · by_cases hfe : f = e
    · subst f
      have hge : g ≠ e := Ne.symm hfg
      have henv : thirdMomentEnvelope e e g
          (1 / ((edgeCount q : ℝ) * collisionSigma G q))
          (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
            collisionSigma G q ^ 3)
          ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
            (1 - collisionProbability G) / collisionSigma G q ^ 3) = 0 := by
        simp [thirdMomentEnvelope, hfg, hge]
      rw [henv]
      unfold thirdEdgeMoment
      exact le_of_eq (uniformAverage_abs_normalizedEdge_mul_self_mul_of_ne G hfg)
    · by_cases hge : g = e
      · subst g
        have henv : thirdMomentEnvelope e f e
            (1 / ((edgeCount q : ℝ) * collisionSigma G q))
            (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
              collisionSigma G q ^ 3)
            ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
              (1 - collisionProbability G) / collisionSigma G q ^ 3) = 0 := by
          simp [thirdMomentEnvelope, hfg]
        rw [henv]
        unfold thirdEdgeMoment
        have hz := uniformAverage_abs_normalizedEdge_mul_self_mul_of_ne
          G (Ne.symm hfe)
        rw [← hz]
        exact (uniformAverage_congr (fun y => by ring)).le
      · by_cases hclosed : ClosedEdgeTriangle e f g
        · have henv : thirdMomentEnvelope e f g
              (1 / ((edgeCount q : ℝ) * collisionSigma G q))
              (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
                collisionSigma G q ^ 3)
              ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
                (1 - collisionProbability G) / collisionSigma G q ^ 3) =
              (1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
                (1 - collisionProbability G) / collisionSigma G q ^ 3 := by
            simp [thirdMomentEnvelope, hfg, hfe, hge, hclosed]
          rw [henv]
          unfold thirdEdgeMoment
          exact le_of_eq (uniformAverage_abs_normalizedEdge_mul_two_of_closed
            G hq hN (Ne.symm hfe) (Ne.symm hge) hfg hclosed)
        · have henv : thirdMomentEnvelope e f g
              (1 / ((edgeCount q : ℝ) * collisionSigma G q))
              (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
                collisionSigma G q ^ 3)
              ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
                (1 - collisionProbability G) / collisionSigma G q ^ 3) = 0 := by
            simp [thirdMomentEnvelope, hfg, hfe, hge, hclosed]
          rw [henv]
          unfold thirdEdgeMoment
          exact le_of_eq
            (uniformAverage_abs_normalizedEdge_mul_two_of_not_closed G hfg hclosed)

theorem collisionProbability_le_half
    (G : Type*) [Fintype G] (hN : 2 ≤ Fintype.card G) :
    collisionProbability G ≤ 1 / 2 := by
  unfold collisionProbability
  have hcard : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  rw [div_le_iff₀ hcard]
  have hcast : (2 : ℝ) ≤ (Fintype.card G : ℝ) := by exact_mod_cast hN
  nlinarith

theorem localNormalizedSum_sq_eq
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (e : Edge q) (y : Fin q → G) :
    (localNormalizedSum G e y) ^ 2 =
      ∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        normalizedEdge G f y * normalizedEdge G g y := by
  unfold localNormalizedSum
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f _hf
  rw [Finset.mul_sum]

theorem third_local_moment_le_raw
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (fun y =>
      ∑ e : Edge q, |normalizedEdge G e y| *
        (localNormalizedSum G e y) ^ 2) ≤
      (edgeCount q : ℝ) *
        (1 / ((edgeCount q : ℝ) * collisionSigma G q) +
          ((4 * q : Nat) : ℝ) *
            (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
              (collisionSigma G q) ^ 3) +
          ((4 * q : Nat) : ℝ) *
            ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
              (1 - collisionProbability G) / (collisionSigma G q) ^ 3)) := by
  let self : ℝ := 1 / ((edgeCount q : ℝ) * collisionSigma G q)
  let pair : ℝ := 2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
    (collisionSigma G q) ^ 3
  let tri : ℝ := (1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
    (1 - collisionProbability G) / (collisionSigma G q) ^ 3
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hp1 : collisionProbability G ≤ 1 := collisionProbability_le_one G
  have hphalf : collisionProbability G ≤ 1 / 2 := collisionProbability_le_half G hN
  have hpair0 : 0 ≤ pair := by dsimp [pair]; positivity
  have htri0 : 0 ≤ tri := by
    dsimp [tri]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sub_nonneg.mpr hp1))
      (by positivity)
  have havg :
      uniformAverage (Fin q → G) (fun y =>
          ∑ e : Edge q, |normalizedEdge G e y| *
            (localNormalizedSum G e y) ^ 2) =
        ∑ e : Edge q, ∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
          thirdEdgeMoment G e f g := by
    rw [uniformAverage_finset_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [show (fun y : Fin q → G =>
        |normalizedEdge G e y| * (localNormalizedSum G e y) ^ 2) =
      (fun y => ∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        |normalizedEdge G e y| * normalizedEdge G f y * normalizedEdge G g y) by
          funext y
          rw [localNormalizedSum_sq_eq]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f _hf
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _hg
          ring]
    rw [uniformAverage_finset_sum_over]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [uniformAverage_finset_sum_over]
    rfl
  rw [havg]
  calc
    (∑ e : Edge q, ∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        thirdEdgeMoment G e f g) ≤
      ∑ e : Edge q, ∑ f ∈ localEdges e, ∑ g ∈ localEdges e,
        thirdMomentEnvelope e f g self pair tri := by
      apply Finset.sum_le_sum
      intro e _he
      apply Finset.sum_le_sum
      intro f _hf
      apply Finset.sum_le_sum
      intro g _hg
      exact thirdEdgeMoment_le_envelope G hq hN e f g
    _ = ∑ e : Edge q,
        (self + ((neighborEdges e).card : ℝ) * pair +
          ((closedTrianglePairs e).card : ℝ) * tri) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact sum_thirdMomentEnvelope e self pair tri
    _ ≤ ∑ _e : Edge q,
        (self + ((4 * q : Nat) : ℝ) * pair +
          ((4 * q : Nat) : ℝ) * tri) := by
      apply Finset.sum_le_sum
      intro e _he
      gcongr
      · exact_mod_cast card_neighborEdges_le_four_mul e
      · exact_mod_cast card_closedTrianglePairs_le_four_mul e
    _ = (edgeCount q : ℝ) *
        (1 / ((edgeCount q : ℝ) * collisionSigma G q) +
          ((4 * q : Nat) : ℝ) *
            (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
              (collisionSigma G q) ^ 3) +
          ((4 * q : Nat) : ℝ) *
            ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
              (1 - collisionProbability G) / (collisionSigma G q) ^ 3)) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      rfl

theorem third_local_moment_le
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (fun y =>
      ∑ e : Edge q, |normalizedEdge G e y| *
        (localNormalizedSum G e y) ^ 2) ≤
      1 / collisionSigma G q +
        ((12 * q : Nat) : ℝ) * collisionProbability G /
          collisionSigma G q := by
  have hraw := third_local_moment_le_raw G hq hN
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hM : 0 < (edgeCount q : ℝ) := by exact_mod_cast edgeCount_pos hq
  have hsquare : (collisionSigma G q) ^ 2 =
      (edgeCount q : ℝ) * collisionProbability G *
        (1 - collisionProbability G) := by
    rw [collisionSigma_sq G hq hN, collisionVariance_eq_probability]
  have heq :
      (edgeCount q : ℝ) *
          (1 / ((edgeCount q : ℝ) * collisionSigma G q) +
            ((4 * q : Nat) : ℝ) *
              (2 * (collisionProbability G * (1 - collisionProbability G)) ^ 2 /
                (collisionSigma G q) ^ 3) +
            ((4 * q : Nat) : ℝ) *
              ((1 - 2 * collisionProbability G) * collisionProbability G ^ 2 *
                (1 - collisionProbability G) / (collisionSigma G q) ^ 3)) =
        1 / collisionSigma G q +
          ((8 * q : Nat) : ℝ) * collisionProbability G *
              (1 - collisionProbability G) / collisionSigma G q +
          ((4 * q : Nat) : ℝ) * (1 - 2 * collisionProbability G) *
              collisionProbability G / collisionSigma G q := by
    field_simp [hs.ne', hM.ne']
    rw [hsquare]
    push_cast
    ring
  refine hraw.trans (le_of_eq heq |>.trans ?_)
  have hp0 : 0 ≤ collisionProbability G := collisionProbability_nonneg G
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hA :
      (8 : ℝ) * q * collisionProbability G * (1 - collisionProbability G) ≤
        8 * q * collisionProbability G := by
    have hcoef : 0 ≤ (8 : ℝ) * q * collisionProbability G := by positivity
    nlinarith
  have hB :
      (4 : ℝ) * q * (1 - 2 * collisionProbability G) *
          collisionProbability G ≤
        4 * q * collisionProbability G := by
    have hcoef : 0 ≤ (4 : ℝ) * q * collisionProbability G := by positivity
    nlinarith
  have hs0 : 0 ≤ collisionSigma G q := hs.le
  push_cast
  calc
    1 / collisionSigma G q +
          8 * q * collisionProbability G * (1 - collisionProbability G) /
            collisionSigma G q +
          4 * q * (1 - 2 * collisionProbability G) * collisionProbability G /
            collisionSigma G q =
        1 / collisionSigma G q +
          (8 * q * collisionProbability G * (1 - collisionProbability G) +
            4 * q * (1 - 2 * collisionProbability G) * collisionProbability G) /
              collisionSigma G q := by ring
    _ ≤ 1 / collisionSigma G q +
          (8 * q * collisionProbability G + 4 * q * collisionProbability G) /
            collisionSigma G q := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right (add_le_add hA hB) hs0)
    _ = 1 / collisionSigma G q +
          12 * q * collisionProbability G / collisionSigma G q := by ring

/-- The finite local-dependence Stein theorem specialized to the collision
count.  The next section bounds its three explicit finite moments. -/
theorem standardizedCollisionMAD_sub_normal_le_local_terms
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) :
    |uniformAverage (Fin q → G)
        (fun y => |standardizedCollisionCount G q y|) -
      Real.sqrt (2 / Real.pi)| ≤
      normalAbsConstant *
        uniformAverage (Fin q → G) (fun y =>
          |1 - ∑ e : Edge q, (normalizedEdge G e y) ^ 2|) +
      uniformAverage (Fin q → G) (fun y =>
        ∑ e : Edge q, (normalizedEdge G e y) ^ 2 *
          |localNormalizedSum G e y|) +
      uniformAverage (Fin q → G) (fun y =>
        ∑ e : Edge q, |normalizedEdge G e y| *
          (localNormalizedSum G e y) ^ 2) := by
  simpa [normalAbsSteinCertificate, normalAbsConstant] using
    uniformAverage_abs_sub_target_le_of_local_stein
      normalAbsSteinCertificate
      (fun e y => normalizedEdge G e y)
      (standardizedCollisionCount G q)
      (fun e y => outsideNormalizedSum G e y)
      (fun e y => localNormalizedSum G e y)
      (standardizedCollisionCount_eq_sum_normalizedEdge G q)
      (fun e y => standardizedCollisionCount_split G e y)
      (fun e => uniformAverage_normalizedEdge_mul_outside_f G e absSteinF)
      (fun e => uniformAverage_normalizedEdge_mul_local_without_self
        G e absSteinG)

/-- A completely finite normal-MAD approximation for the collision count.

The three summands have a transparent origin: the exact Bernoulli square
identity, pairs of adjacent collision edges, and closed edge triangles.  In
particular, no asymptotic theorem or unproved normal-approximation hypothesis
is used here. -/
theorem standardizedCollisionMAD_sub_normal_le
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    |uniformAverage (Fin q → G)
        (fun y => |standardizedCollisionCount G q y|) -
      Real.sqrt (2 / Real.pi)| ≤
      normalAbsConstant * (1 / collisionSigma G q) +
        (1 / collisionSigma G q +
          ((8 * q : Nat) : ℝ) * collisionProbability G *
            (1 - collisionProbability G) / collisionSigma G q) +
        (1 / collisionSigma G q +
          ((12 * q : Nat) : ℝ) * collisionProbability G /
            collisionSigma G q) := by
  calc
    |uniformAverage (Fin q → G)
          (fun y => |standardizedCollisionCount G q y|) -
        Real.sqrt (2 / Real.pi)| ≤
        normalAbsConstant *
          uniformAverage (Fin q → G) (fun y =>
            |1 - ∑ e : Edge q, (normalizedEdge G e y) ^ 2|) +
        uniformAverage (Fin q → G) (fun y =>
          ∑ e : Edge q, (normalizedEdge G e y) ^ 2 *
            |localNormalizedSum G e y|) +
        uniformAverage (Fin q → G) (fun y =>
          ∑ e : Edge q, |normalizedEdge G e y| *
            (localNormalizedSum G e y) ^ 2) :=
      standardizedCollisionMAD_sub_normal_le_local_terms G q
    _ ≤ normalAbsConstant * (1 / collisionSigma G q) +
          (1 / collisionSigma G q +
            ((8 * q : Nat) : ℝ) * collisionProbability G *
              (1 - collisionProbability G) / collisionSigma G q) +
          (1 / collisionSigma G q +
            ((12 * q : Nat) : ℝ) * collisionProbability G /
              collisionSigma G q) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left
            (first_local_moment_le G hq hN) normalAbsConstant_pos.le)
          (second_local_moment_le G hq hN))
        (third_local_moment_le G hq hN)

/-- The readable finite error envelope.  Since
`collisionProbability G = 1 / |G|`, its correction term is of order
`q / (|G| * sigma)`, while the remaining term is of order `1 / sigma`. -/
def collisionNormalErrorBound
    (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  (normalAbsConstant + 2 +
      20 * (q : ℝ) * collisionProbability G) /
    collisionSigma G q

theorem standardizedCollisionMAD_sub_normal_le_errorBound
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    |uniformAverage (Fin q → G)
        (fun y => |standardizedCollisionCount G q y|) -
      normalAbsConstant| ≤ collisionNormalErrorBound G q := by
  have hfinite := standardizedCollisionMAD_sub_normal_le G hq hN
  have hp0 : 0 ≤ collisionProbability G := collisionProbability_nonneg G
  have hp1 : collisionProbability G ≤ 1 := collisionProbability_le_one G
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hquadratic :
      collisionProbability G * (1 - collisionProbability G) ≤
        collisionProbability G := by
    nlinarith
  have hscaled :
      8 * (q : ℝ) *
          (collisionProbability G * (1 - collisionProbability G)) ≤
        8 * (q : ℝ) * collisionProbability G := by
    exact mul_le_mul_of_nonneg_left hquadratic (by positivity)
  rw [show normalAbsConstant = Real.sqrt (2 / Real.pi) by
    rfl]
  refine hfinite.trans ?_
  unfold collisionNormalErrorBound
  push_cast
  rw [show
      normalAbsConstant * (1 / collisionSigma G q) +
            (1 / collisionSigma G q +
              8 * q * collisionProbability G *
                (1 - collisionProbability G) / collisionSigma G q) +
            (1 / collisionSigma G q +
              12 * q * collisionProbability G / collisionSigma G q) =
        (normalAbsConstant + 2 +
            8 * q * (collisionProbability G *
              (1 - collisionProbability G)) +
            12 * q * collisionProbability G) /
          collisionSigma G q by ring]
  apply div_le_div_of_nonneg_right _ hs.le
  linarith

/-- The local-dependence correction is uniformly at most
`2 / sqrt (|G| - 1)`.  This is the finite estimate that makes the local term
vanish solely from growth of the color set. -/
theorem local_correction_le_two_div_sqrt_card_sub_one
    (G : Type*) [Fintype G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    (q : ℝ) * collisionProbability G / collisionSigma G q ≤
      2 / Real.sqrt ((Fintype.card G - 1 : Nat) : ℝ) := by
  have hs : 0 < collisionSigma G q := collisionSigma_pos G hq hN
  have hNm1Nat : 0 < Fintype.card G - 1 := Nat.sub_pos_of_lt hN
  have hNm1 : 0 < ((Fintype.card G - 1 : Nat) : ℝ) := by
    exact_mod_cast hNm1Nat
  have hsqrt : 0 < Real.sqrt ((Fintype.card G - 1 : Nat) : ℝ) :=
    Real.sqrt_pos.2 hNm1
  have hleft :
      0 ≤ (q : ℝ) * collisionProbability G / collisionSigma G q := by
    exact div_nonneg
      (mul_nonneg (by positivity) (collisionProbability_nonneg G)) hs.le
  have hright :
      0 ≤ 2 / Real.sqrt ((Fintype.card G - 1 : Nat) : ℝ) := by
    positivity
  rw [← sq_le_sq₀ hleft hright]
  have hM : 0 < (edgeCount q : ℝ) := by
    exact_mod_cast edgeCount_pos hq
  have hcard : 0 < (Fintype.card G : ℝ) := by positivity
  have hsquare : collisionSigma G q ^ 2 =
      (edgeCount q : ℝ) * ((Fintype.card G - 1 : Nat) : ℝ) /
        (Fintype.card G : ℝ) ^ 2 :=
    collisionSigma_sq G hq hN
  have hMcount : (edgeCount q : ℝ) * 2 =
      (q : ℝ) * ((q : ℝ) - 1) := by
    calc
      (edgeCount q : ℝ) * 2 = (edgeCount q * 2 : Nat) := by norm_num
      _ = (q * (q - 1) : Nat) := by rw [edgeCount_mul_two]
      _ = (q : ℝ) * ((q : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q)]
        norm_num
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold collisionProbability
  rw [div_pow, div_pow, Real.sq_sqrt hNm1.le, hsquare]
  field_simp [hs.ne', hsqrt.ne', hM.ne', hcard.ne', hNm1.ne']
  nlinarith

/-- A triangular-array normal limit for collision counts on finite color
sets.  The first analytic hypothesis says that the collision-count standard
deviation diverges.  The second is the vanishing local-dependence correction;
for the birthday model it is asymptotically proportional to `1 / sqrt N`.

Unlike a black-box CLT, this theorem is a direct consequence of the explicit
finite Stein estimate above. -/
theorem tendsto_standardizedCollisionMAD_fin
    (N q : ℕ → ℕ)
    (hq : ∀ᶠ k in atTop, 2 ≤ q k)
    (hN : ∀ᶠ k in atTop, 2 ≤ N k)
    (hsigma : Tendsto
      (fun k => collisionSigma (Fin (N k)) (q k)) atTop atTop)
    (hlocal : Tendsto
      (fun k =>
        (q k : ℝ) * collisionProbability (Fin (N k)) /
          collisionSigma (Fin (N k)) (q k))
      atTop (nhds 0)) :
    Tendsto
      (fun k =>
        uniformAverage (Fin (q k) → Fin (N k)) (fun y =>
          |standardizedCollisionCount (Fin (N k)) (q k) y|))
      atTop (nhds normalAbsConstant) := by
  have hinv : Tendsto
      (fun k => (collisionSigma (Fin (N k)) (q k))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsigma
  have herr : Tendsto
      (fun k => collisionNormalErrorBound (Fin (N k)) (q k))
      atTop (nhds 0) := by
    have hmain := (tendsto_const_nhds :
      Tendsto (fun _k : ℕ => normalAbsConstant + 2) atTop
        (nhds (normalAbsConstant + 2))).mul hinv
    have hcorr := (tendsto_const_nhds :
      Tendsto (fun _k : ℕ => (20 : ℝ)) atTop (nhds 20)).mul hlocal
    convert hmain.add hcorr using 1
    · funext k
      unfold collisionNormalErrorBound
      ring
    · ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herror : Tendsto
      (fun k =>
        |uniformAverage (Fin (q k) → Fin (N k)) (fun y =>
            |standardizedCollisionCount (Fin (N k)) (q k) y|) -
          normalAbsConstant|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun k => abs_nonneg _)
    · filter_upwards [hq, hN] with k hqk hNk
      letI : Nonempty (Fin (N k)) :=
        Fin.pos_iff_nonempty.mp (by omega)
      simpa using
        (standardizedCollisionMAD_sub_normal_le_errorBound
          (Fin (N k)) hqk (by simpa using hNk))
    · exact herr
  simpa [Real.norm_eq_abs] using herror

/-- Collision-count normal convergence under the natural dense birthday
conditions: the number of colors and the collision-count standard deviation
both diverge.  The query and alphabet lower bounds are only eventual finite
side conditions. -/
theorem tendsto_standardizedCollisionMAD_fin_of_card_and_sigma
    (N q : ℕ → ℕ)
    (hq : ∀ᶠ k in atTop, 2 ≤ q k)
    (hN : ∀ᶠ k in atTop, 2 ≤ N k)
    (hcard : Tendsto N atTop atTop)
    (hsigma : Tendsto
      (fun k => collisionSigma (Fin (N k)) (q k)) atTop atTop) :
    Tendsto
      (fun k =>
        uniformAverage (Fin (q k) → Fin (N k)) (fun y =>
          |standardizedCollisionCount (Fin (N k)) (q k) y|))
      atTop (nhds normalAbsConstant) := by
  have hsub : Tendsto (fun k => N k - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hcard
  have hcast : Tendsto (fun k => ((N k - 1 : Nat) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsub
  have hsqrt : Tendsto
      (fun k => Real.sqrt ((N k - 1 : Nat) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hbound : Tendsto
      (fun k => 2 / Real.sqrt ((N k - 1 : Nat) : ℝ))
      atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hsqrt
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds :
        Tendsto (fun _k : ℕ => (2 : ℝ)) atTop (nhds 2)).mul hinv)
  have hlocal : Tendsto
      (fun k =>
        (q k : ℝ) * collisionProbability (Fin (N k)) /
          collisionSigma (Fin (N k)) (q k))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun k => div_nonneg
        (mul_nonneg (by positivity)
          (collisionProbability_nonneg (Fin (N k))))
        (Real.sqrt_nonneg _))
    · filter_upwards [hq, hN] with k hqk hNk
      letI : Nonempty (Fin (N k)) :=
        Fin.pos_iff_nonempty.mp (by omega)
      simpa using
        (local_correction_le_two_div_sqrt_card_sub_one
          (Fin (N k)) hqk (by simpa using hNk))
    · exact hbound
  exact tendsto_standardizedCollisionMAD_fin N q hq hN hsigma hlocal

end RandomSystems.SoP.CollisionCountNormal
