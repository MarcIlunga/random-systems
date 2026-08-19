/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.XoPCombinatorics
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Quotient

/-!
# Sum/XOR of Permutations: Exact Transcript Scaffold

This folder is for the slowly formalized SoP/XoP orbit-counting line.

The first target is the fixed-input transcript law.  For a visible output tuple
`y`, the compatible hidden-state count

`#{a : Fin q -> G | a is injective and a + y is injective}`

is the numerator of the real transcript density, while `(N)_q^2 / N^q` is the
uniform-output expectation of that count.

The existing XoP application files already contain the concrete model bridge.
This folder is reserved for the tighter LM20/orbit-style exact-bound work, kept
separate from the broader XoP analytic scaffold.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace SoP

open XoP.Combinatorics

variable {G : Type*} {q : Nat}

/-- The nonempty subsets of a two-element finite set are the two singletons and
the full two-element set. -/
theorem finset_pair_powerset_filter_nonempty {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    (({a, b} : Finset α).powerset.filter (fun T => T.Nonempty)) =
      ({{a}, {b}, ({a, b} : Finset α)} : Finset (Finset α)) := by
  ext T
  constructor
  · intro h
    simp only [Finset.mem_filter, Finset.mem_powerset] at h
    rcases h with ⟨hsub, hne⟩
    by_cases ha : a ∈ T
    · by_cases hb : b ∈ T
      · have hT : T = ({a, b} : Finset α) := by
          ext x
          constructor
          · intro hx
            exact hsub hx
          · intro hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact ha
            · exact hb
        simp [hT]
      · have hT : T = ({a} : Finset α) := by
          ext x
          constructor
          · intro hx
            have hxab := hsub hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
            rcases hxab with rfl | hxb
            · simp
            · subst x
              exact False.elim (hb hx)
          · intro hx
            simp only [Finset.mem_singleton] at hx
            subst x
            exact ha
        simp [hT]
    · by_cases hb : b ∈ T
      · have hT : T = ({b} : Finset α) := by
          ext x
          constructor
          · intro hx
            have hxab := hsub hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
            rcases hxab with hxa | rfl
            · subst x
              exact False.elim (ha hx)
            · simp
          · intro hx
            simp only [Finset.mem_singleton] at hx
            subst x
            exact hb
        simp [hT]
      · exfalso
        rcases hne with ⟨x, hx⟩
        have hxab := hsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
        rcases hxab with hxa | hxb
        · subst x
          exact ha hx
        · subst x
          exact hb hx
  · intro h
    simp only [Finset.mem_filter, Finset.mem_powerset]
    have hcases : T = ({a} : Finset α) ∨ T = ({b} : Finset α) ∨
        T = ({a, b} : Finset α) := by
      simpa using h
    rcases hcases with rfl | rfl | rfl
    · constructor
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        simp
      · exact ⟨a, by simp⟩
    · constructor
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        simp
      · exact ⟨b, by simp⟩
    · constructor
      · exact subset_rfl
      · exact ⟨a, by simp⟩

/-- A singleton is not the two-element set containing it and a distinct point. -/
theorem finset_singleton_ne_pair_left {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    ({a} : Finset α) ≠ ({a, b} : Finset α) := by
  intro h
  have hb : b ∈ ({a} : Finset α) := by
    rw [h]
    simp
  simp only [Finset.mem_singleton] at hb
  exact hab hb.symm

/-- A singleton is not the two-element set containing a distinct point and it. -/
theorem finset_singleton_ne_pair_right {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    ({b} : Finset α) ≠ ({a, b} : Finset α) := by
  intro h
  have ha : a ∈ ({b} : Finset α) := by
    rw [h]
    simp
  simp only [Finset.mem_singleton] at ha
  exact hab ha

/-- Unordered query-index pairs, represented by the increasing ordered pair. -/
abbrev PairIndex (q : Nat) :=
  { p : Fin q × Fin q // p.1 < p.2 }

/-- The two kinds of forbidden pair collision in the SoP/XoP compatible-count
problem. -/
inductive CollisionKind where
  | hidden
  | shifted
  deriving DecidableEq

/-- The two collision kinds are distinct. -/
theorem collisionKind_hidden_ne_shifted : CollisionKind.hidden ≠ CollisionKind.shifted := by
  intro h
  cases h

instance collisionKindFintype : Fintype CollisionKind where
  elems := {CollisionKind.hidden, CollisionKind.shifted}
  complete := by
    intro k
    cases k <;> simp

/-- There are exactly two collision kinds: hidden and shifted. -/
theorem collisionKind_card : Fintype.card CollisionKind = 2 := by
  change ({CollisionKind.hidden, CollisionKind.shifted} : Finset CollisionKind).card = 2
  simp [collisionKind_hidden_ne_shifted]

/-- A collision event is a query pair together with the choice of hidden or
shifted collision. -/
abbrev CollisionEvent (q : Nat) :=
  PairIndex q × CollisionKind

/-- The number of query-pair indices satisfies `2 * #PairIndex = q * (q - 1)`. -/
theorem pairIndex_card_mul_two : Fintype.card (PairIndex q) * 2 = q * (q - 1) := by
  rw [Fintype.card_subtype]
  set lt_pairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)
  set gt_pairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.2 < p.1)
  have h_sym : lt_pairs.card = gt_pairs.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [gt_pairs, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [lt_pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.ext (by exact (Prod.mk.inj h).2) (by exact (Prod.mk.inj h).1)
    · intro p hp
      simp only [gt_pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simpa [lt_pairs], rfl⟩
  have h_disj : Disjoint lt_pairs gt_pairs := by
    simp only [lt_pairs, gt_pairs]
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  have h_union :
      lt_pairs ∪ gt_pairs =
        (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, lt_pairs, gt_pairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Fin.ne_of_lt h
      · exact Ne.symm (Fin.ne_of_lt h)
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
  have h_offdiag :
      ((Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2)).card =
        q * (q - 1) := by
    rcases q with _ | n
    · simp
    · rw [show (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
          (fun p => p.1 ≠ p.2) = Finset.univ.offDiag from by
        ext ⟨a, b⟩
        simp [Finset.mem_offDiag]]
      rw [Finset.offDiag_card]
      simp only [Finset.card_univ, Fintype.card_fin, Nat.succ_sub_one]
      ring_nf
      omega
  have h_sum : lt_pairs.card + gt_pairs.card = q * (q - 1) := by
    rw [← h_offdiag, ← h_union]
    exact (Finset.card_union_of_disjoint h_disj).symm
  omega

/-- Visible tuples whose coordinates collide on a fixed query pair are
equivalent to arbitrary assignments on all coordinates except the right endpoint
of that pair. -/
def pairCollisionFiberEquiv [DecidableEq (Fin q)] (p : PairIndex q) :
    { y : Fin q → G // y p.1.2 = y p.1.1 } ≃
      ({ i : Fin q // i ≠ p.1.2 } → G) where
  toFun y i := y.1 i.1
  invFun f :=
    ⟨fun i => if h : i = p.1.2 then f ⟨p.1.1, by omega⟩ else f ⟨i, h⟩, by
      simp [Fin.ne_of_lt p.2]⟩
  left_inv y := by
    ext i
    by_cases h : i = p.1.2
    · subst i
      simp [y.2]
    · simp [h]
  right_inv f := by
    funext i
    simp [i.2]

/-- For a fixed query pair, exactly `|G|^(q-1)` visible tuples collide on that
pair. -/
theorem pairCollisionFiber_card [Fintype G] [DecidableEq G] (p : PairIndex q) :
    ((Finset.univ : Finset (Fin q → G)).filter
      (fun y => y p.1.2 = y p.1.1)).card =
      Fintype.card G ^ (q - 1) := by
  classical
  have hindex :
      Fintype.card { i : Fin q // i ≠ p.1.2 } = q - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin q => i = p.1.2)]
    rw [Fintype.card_fin, Fintype.card_subtype_eq]
  calc
    ((Finset.univ : Finset (Fin q → G)).filter
      (fun y => y p.1.2 = y p.1.1)).card =
        Fintype.card { y : Fin q → G // y p.1.2 = y p.1.1 } := by
          rw [Fintype.card_subtype]
    _ = Fintype.card ({ i : Fin q // i ≠ p.1.2 } → G) := by
          exact Fintype.card_congr (pairCollisionFiberEquiv (G := G) (q := q) p)
    _ = Fintype.card G ^ Fintype.card { i : Fin q // i ≠ p.1.2 } := by
          rw [Fintype.card_fun]
    _ = Fintype.card G ^ (q - 1) := by
          rw [hindex]

/-- The total number of visible coordinate-pair collisions over all visible
tuples is `#PairIndex * |G|^(q-1)`. -/
theorem sum_pairCollisionIndicators_eq_pairIndex_card_mul_card_pow
    [Fintype G] [DecidableEq G] :
    (∑ y : Fin q → G, ∑ p : PairIndex q,
      (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) =
      Fintype.card (PairIndex q) * Fintype.card G ^ (q - 1) := by
  classical
  calc
    (∑ y : Fin q → G, ∑ p : PairIndex q,
      (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) =
        ∑ p : PairIndex q, ∑ y : Fin q → G,
          (if y p.1.2 = y p.1.1 then 1 else 0 : Nat) := by
          rw [Finset.sum_comm]
    _ = ∑ p : PairIndex q, Fintype.card G ^ (q - 1) := by
          apply Finset.sum_congr rfl
          intro p _hp
          rw [← pairCollisionFiber_card (G := G) (q := q) p]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = Fintype.card (PairIndex q) * Fintype.card G ^ (q - 1) := by
          simp [Finset.sum_const]

/-- Normalized form of `sum_pairCollisionIndicators_eq_pairIndex_card_mul_card_pow`:
under the uniform visible law, the expected number of colliding coordinate pairs
is `#PairIndex / |G|`. -/
theorem uniformAverage_pairCollisionIndicators_eq_pairIndex_card_div_card
    [Fintype G] [DecidableEq G] [Nonempty G] (hq : 0 < q) :
    (∑ y : Fin q → G,
      (((∑ p : PairIndex q,
        (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) : Nat) : NNReal)) /
        ((Fintype.card G ^ q : Nat) : NNReal) =
      (Fintype.card (PairIndex q) : NNReal) / (Fintype.card G : NNReal) := by
  classical
  have hsumNat :=
    sum_pairCollisionIndicators_eq_pairIndex_card_mul_card_pow (G := G) (q := q)
  have hsumNN :
      (∑ y : Fin q → G,
        (((∑ p : PairIndex q,
          (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) : Nat) : NNReal)) =
        (((Fintype.card (PairIndex q) * Fintype.card G ^ (q - 1) : Nat) : NNReal)) := by
    exact_mod_cast hsumNat
  rw [hsumNN]
  have hpowNat :
      Fintype.card G ^ q = Fintype.card G ^ (q - 1) * Fintype.card G := by
    nth_rewrite 1 [show q = q - 1 + 1 by omega]
    rw [pow_succ]
  have hN : (Fintype.card G : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos : Fintype.card G ≠ 0)
  rw [hpowNat, Nat.cast_mul, Nat.cast_mul]
  field_simp [hN]

/-- A collision event is one of two event kinds on an unordered query pair. -/
theorem collisionEvent_card : Fintype.card (CollisionEvent q) = Fintype.card (PairIndex q) * 2 := by
  rw [Fintype.card_prod, collisionKind_card]

/-- There are `q * (q - 1)` collision events: hidden and shifted events for
each unordered query pair. -/
theorem collisionEvent_card_eq_query_pair_twice :
    Fintype.card (CollisionEvent q) = q * (q - 1) := by
  rw [collisionEvent_card, pairIndex_card_mul_two]

/-- The number of collision-event subfamilies is `2^(# collision events)`. -/
theorem collisionEvent_univ_powerset_card :
    ((Finset.univ : Finset (CollisionEvent q)).powerset.card) =
      2 ^ Fintype.card (CollisionEvent q) := by
  rw [Finset.card_powerset]
  simp

/-- The indexed pair-local event set: hidden and shifted collisions on one
query-coordinate pair. -/
def collisionPairEvents (p : PairIndex q) : Finset (CollisionEvent q) :=
  {(p, CollisionKind.hidden), (p, CollisionKind.shifted)}

/-- The left endpoint of the oriented representative of a collision event. -/
def collisionEventLeft (e : CollisionEvent q) : Fin q :=
  e.1.1.1

/-- The right endpoint of the oriented representative of a collision event. -/
def collisionEventRight (e : CollisionEvent q) : Fin q :=
  e.1.1.2

/-- The chosen event orientation always points from the smaller index to the
larger index. -/
theorem collisionEventLeft_lt_right (e : CollisionEvent q) :
    collisionEventLeft e < collisionEventRight e :=
  e.1.2

/-- The additive label carried by a collision event.

With the orientation `left -> right`, the hidden equation is
`a left - a right = 0`, while the shifted equation
`a left + y left = a right + y right` is equivalently
`a left - a right = y right - y left` in an additive commutative group. -/
def collisionEventLabel [AddGroup G] (y : Fin q → G) (e : CollisionEvent q) : G :=
  match e.2 with
  | CollisionKind.hidden => 0
  | CollisionKind.shifted => y (collisionEventRight e) - y (collisionEventLeft e)

/-- The oriented labelled equation represented by one collision event. -/
def collisionEventEquation [AddGroup G] (y : Fin q → G)
    (e : CollisionEvent q) (a : Fin q → G) : Prop :=
  a (collisionEventLeft e) - a (collisionEventRight e) = collisionEventLabel y e

instance collisionEventEquationDecidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) (e : CollisionEvent q) :
    DecidablePred (fun a : Fin q → G => collisionEventEquation y e a) :=
  fun _ => Classical.propDecidable _

/-- The predicate that a hidden tuple triggers a particular collision event. -/
def collisionEventOccurs [AddGroup G] (y : Fin q → G)
    (e : CollisionEvent q) (a : Fin q → G) : Prop :=
  match e.2 with
  | CollisionKind.hidden => a e.1.1.1 = a e.1.1.2
  | CollisionKind.shifted =>
      XoP.Combinatorics.shifted y a e.1.1.1 =
        XoP.Combinatorics.shifted y a e.1.1.2

/-- In the commutative setting used by SoP/XoP, collision occurrence is exactly
the oriented labelled equation carried by the event. -/
theorem collisionEventOccurs_iff_equation [AddCommGroup G]
    (y : Fin q → G) (e : CollisionEvent q) (a : Fin q → G) :
    collisionEventOccurs (G := G) (q := q) y e a ↔
      collisionEventEquation (G := G) (q := q) y e a := by
  rcases e with ⟨⟨⟨i, j⟩, _hij⟩, kind⟩
  cases kind with
  | hidden =>
      simp [collisionEventOccurs, collisionEventEquation, collisionEventLeft,
        collisionEventRight, collisionEventLabel, sub_eq_zero]
  | shifted =>
      simp only [collisionEventOccurs, collisionEventEquation, collisionEventLeft,
        collisionEventRight, collisionEventLabel, XoP.Combinatorics.shifted]
      constructor
      · intro h
        rw [← sub_eq_zero] at h ⊢
        abel_nf at h ⊢
        exact h
      · intro h
        rw [← sub_eq_zero] at h ⊢
        abel_nf at h ⊢
        exact h

instance collisionEventOccursDecidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) (e : CollisionEvent q) :
    DecidablePred (fun a : Fin q → G => collisionEventOccurs y e a) :=
  fun _ => Classical.propDecidable _

instance collisionEventAvoidanceDecidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) :
    DecidablePred
      (fun a : Fin q → G =>
        ∀ e : CollisionEvent q, ¬ collisionEventOccurs (G := G) (q := q) y e a) :=
  fun _ => Classical.propDecidable _

/-- SoP-compatible hidden states are the same hidden states used by the XoP
counting bridge: both the hidden tuple and the shifted tuple must be injective.

This alias gives the exact-bound development its own vocabulary without
duplicating the existing combinatorial definitions. -/
abbrev CompatibleHiddenState [AddGroup G] (y a : Fin q → G) : Prop :=
  XoP.Combinatorics.CompatibleHiddenState y a

/-- Raw compatible hidden-state count for one visible tuple. -/
abbrev compatibleCountNat [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) : Nat :=
  XoP.Combinatorics.compatibleCountNat y

/-- The exact real transcript numerator for one visible tuple, as `NNReal`. -/
abbrev compatibleCountNNReal [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) : NNReal :=
  XoP.Combinatorics.compatibleCountNNReal y

/-- The uniform-output expectation normalizer `(N)_q^2 / N^q` for compatible
hidden-state counts, packaged with its nonzero proof under `q ≤ N`. -/
abbrev compatibleExpectationNormalizer [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    XoP.Counting.FallingFactorialNormalizer G q :=
  XoP.Combinatorics.compatibleExpectationNormalizer hq

/-- First exact-transcript target: the compatible-count formula is invariant
under global visible translation. -/
theorem compatibleCountNat_add_const [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (c : G) :
    compatibleCountNat (G := G) (q := q) (fun i => y i + c) =
      compatibleCountNat (G := G) (q := q) y :=
  XoP.Combinatorics.compatibleCountNat_add_const y c

/-- A hidden tuple is compatible exactly when it triggers none of the finite
collision events. -/
theorem compatibleHiddenState_iff_forall_not_collisionEventOccurs [AddGroup G]
    (y a : Fin q → G) :
    CompatibleHiddenState (G := G) (q := q) y a ↔
      ∀ e : CollisionEvent q, ¬ collisionEventOccurs (G := G) (q := q) y e a := by
  constructor
  · intro h e he
    rcases e with ⟨⟨⟨i, j⟩, hij⟩, kind⟩
    cases kind with
    | hidden =>
        exact (ne_of_lt hij) (h.1 (by simpa [collisionEventOccurs] using he))
    | shifted =>
        exact (ne_of_lt hij) (h.2 (by simpa [collisionEventOccurs] using he))
  · intro h
    constructor
    · intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (h ⟨⟨(i, j), hlt⟩, CollisionKind.hidden⟩)
          (by simpa [collisionEventOccurs] using hij)
      · exact (h ⟨⟨(j, i), hgt⟩, CollisionKind.hidden⟩)
          (by simpa [collisionEventOccurs] using hij.symm)
    · intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (h ⟨⟨(i, j), hlt⟩, CollisionKind.shifted⟩)
          (by simpa [collisionEventOccurs] using hij)
      · exact (h ⟨⟨(j, i), hgt⟩, CollisionKind.shifted⟩)
          (by simpa [collisionEventOccurs] using hij.symm)

/-- `compatibleCountNat` as a finite forbidden-event avoidance count. -/
theorem compatibleCountNat_eq_card_filter_forall_not_collisionEventOccurs
    [AddGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    compatibleCountNat (G := G) (q := q) y =
      ((Finset.univ : Finset (Fin q → G)).filter
        (fun a => ∀ e : CollisionEvent q,
          ¬ collisionEventOccurs (G := G) (q := q) y e a)).card := by
  unfold compatibleCountNat XoP.Combinatorics.compatibleCountNat
  congr 1
  ext a
  simp [compatibleHiddenState_iff_forall_not_collisionEventOccurs]

/-- A hidden tuple satisfies every collision equation in a chosen finite
subfamily of collision events. -/
def collisionSubfamilyOccurs [AddGroup G] (y : Fin q → G)
    (T : Finset (CollisionEvent q)) (a : Fin q → G) : Prop :=
  ∀ e ∈ T, collisionEventOccurs (G := G) (q := q) y e a

/-- The subfamily occurrence predicate can be read as satisfaction of every
oriented labelled equation in the subfamily. -/
theorem collisionSubfamilyOccurs_iff_forall_equations [AddCommGroup G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) (a : Fin q → G) :
    collisionSubfamilyOccurs (G := G) (q := q) y T a ↔
      ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a := by
  simp [collisionSubfamilyOccurs, collisionEventOccurs_iff_equation]

/-- The undirected endpoint relation induced by a collision-event subfamily. -/
def collisionSubfamilyAdjacent (T : Finset (CollisionEvent q)) (i j : Fin q) : Prop :=
  ∃ e ∈ T,
    (collisionEventLeft e = i ∧ collisionEventRight e = j) ∨
      (collisionEventLeft e = j ∧ collisionEventRight e = i)

/-- Two coordinates are connected in the support graph of a collision-event
subfamily. -/
def collisionSubfamilyConnected (T : Finset (CollisionEvent q)) (i j : Fin q) : Prop :=
  Relation.ReflTransGen (collisionSubfamilyAdjacent (q := q) T) i j

/-- The support relation of a collision-event subfamily is symmetric. -/
theorem collisionSubfamilyAdjacent_symm (T : Finset (CollisionEvent q)) :
    Symmetric (collisionSubfamilyAdjacent (q := q) T) := by
  intro i j h
  rcases h with ⟨e, heT, hends | hends⟩
  · exact ⟨e, heT, Or.inr hends⟩
  · exact ⟨e, heT, Or.inl hends⟩

/-- Connectivity in the support graph is reflexive. -/
theorem collisionSubfamilyConnected_refl (T : Finset (CollisionEvent q)) (i : Fin q) :
    collisionSubfamilyConnected (q := q) T i i :=
  Relation.ReflTransGen.refl

/-- Connectivity in the support graph is symmetric. -/
theorem collisionSubfamilyConnected_symm (T : Finset (CollisionEvent q)) :
    Symmetric (collisionSubfamilyConnected (q := q) T) :=
  Relation.ReflTransGen.symmetric (collisionSubfamilyAdjacent_symm (q := q) T)

/-- Connectivity in the support graph is transitive. -/
theorem collisionSubfamilyConnected_trans (T : Finset (CollisionEvent q)) :
    IsTrans (Fin q) (collisionSubfamilyConnected (q := q) T) :=
  ⟨fun _ _ _ => Relation.ReflTransGen.trans⟩

/-- Enlarging a collision-event subfamily preserves support adjacency. -/
theorem collisionSubfamilyAdjacent_mono {S T : Finset (CollisionEvent q)}
    (hST : S ⊆ T) {i j : Fin q}
    (hij : collisionSubfamilyAdjacent (q := q) S i j) :
    collisionSubfamilyAdjacent (q := q) T i j := by
  rcases hij with ⟨e, heS, hends⟩
  exact ⟨e, hST heS, hends⟩

/-- Enlarging a collision-event subfamily preserves support connectivity. -/
theorem collisionSubfamilyConnected_mono {S T : Finset (CollisionEvent q)}
    (hST : S ⊆ T) {i j : Fin q}
    (hij : collisionSubfamilyConnected (q := q) S i j) :
    collisionSubfamilyConnected (q := q) T i j := by
  induction hij with
  | refl => exact collisionSubfamilyConnected_refl (q := q) T i
  | tail _hprev hadj ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (collisionSubfamilyAdjacent_mono (q := q) hST hadj))

/-- Semantic consistency of a labelled collision-event subfamily: the equation
system has at least one solution.  The later gain-graph step identifies this
predicate with closed-walk label consistency. -/
def collisionSubfamilyConsistent [AddGroup G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) : Prop :=
  ∃ base : Fin q → G, ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e base

instance collisionSubfamilyConsistentDecidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    Decidable (collisionSubfamilyConsistent (G := G) (q := q) y T) :=
  Classical.propDecidable _

/-- A labelled oriented step through an event of a collision subfamily.

The event itself has a canonical orientation `left -> right`.  Traversing it in
that direction contributes its label; traversing it backwards contributes the
negative label. -/
def collisionSubfamilyStepLabel [AddGroup G] (y : Fin q → G)
    (T : Finset (CollisionEvent q)) (i j : Fin q) (label : G) : Prop :=
  ∃ e ∈ T,
    (collisionEventLeft e = i ∧ collisionEventRight e = j ∧
        label = collisionEventLabel y e) ∨
      (collisionEventLeft e = j ∧ collisionEventRight e = i ∧
        label = -collisionEventLabel y e)

/-- A labelled step is an ordinary support-graph connection. -/
theorem collisionSubfamilyStepLabel_connected [AddGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {i j : Fin q} {label : G}
    (hstep : collisionSubfamilyStepLabel (G := G) (q := q) y T i j label) :
    collisionSubfamilyConnected (q := q) T i j := by
  rcases hstep with ⟨e, heT, hends | hends⟩
  · exact Relation.ReflTransGen.single ⟨e, heT, Or.inl ⟨hends.1, hends.2.1⟩⟩
  · exact Relation.ReflTransGen.single ⟨e, heT, Or.inr ⟨hends.1, hends.2.1⟩⟩

/-- Reversing an oriented labelled step negates its label. -/
theorem collisionSubfamilyStepLabel_symm [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {i j : Fin q} {label : G}
    (hstep : collisionSubfamilyStepLabel (G := G) (q := q) y T i j label) :
    collisionSubfamilyStepLabel (G := G) (q := q) y T j i (-label) := by
  rcases hstep with ⟨e, heT, hends | hends⟩
  · rcases hends with ⟨hli, hrj, hlabel⟩
    exact ⟨e, heT, Or.inr ⟨hli, hrj, by simp [hlabel]⟩⟩
  · rcases hends with ⟨hlj, hri, hlabel⟩
    exact ⟨e, heT, Or.inl ⟨hlj, hri, by simp [hlabel]⟩⟩

/-- Every support adjacency has at least one labelled oriented step. -/
theorem collisionSubfamilyAdjacent_exists_stepLabel [AddGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {i j : Fin q}
    (hij : collisionSubfamilyAdjacent (q := q) T i j) :
    ∃ label : G, collisionSubfamilyStepLabel (G := G) (q := q) y T i j label := by
  rcases hij with ⟨e, heT, hends | hends⟩
  · exact ⟨collisionEventLabel y e, ⟨e, heT, Or.inl ⟨hends.1, hends.2, rfl⟩⟩⟩
  · exact ⟨-collisionEventLabel y e, ⟨e, heT, Or.inr ⟨hends.1, hends.2, rfl⟩⟩⟩

/-- Any solution to a labelled subfamily realizes the signed label of each
oriented step as the endpoint difference. -/
theorem collisionSubfamilyStepLabel_equation [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {a : Fin q → G}
    {i j : Fin q} {label : G}
    (ha : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a)
    (hstep : collisionSubfamilyStepLabel (G := G) (q := q) y T i j label) :
    a i - a j = label := by
  rcases hstep with ⟨e, heT, hends | hends⟩
  · rcases hends with ⟨hli, hrj, hlabel⟩
    rw [hlabel]
    have h := ha e heT
    unfold collisionEventEquation at h
    simpa [hli, hrj] using h
  · rcases hends with ⟨hlj, hri, hlabel⟩
    rw [hlabel]
    have h := ha e heT
    unfold collisionEventEquation at h
    rw [hlj, hri] at h
    calc
      a i - a j = -(a j - a i) := by abel
      _ = -collisionEventLabel y e := by rw [h]

/-- Labelled reachability through a collision subfamily, carrying the
accumulated signed label along the walk. -/
inductive collisionSubfamilyLabelReach [AddGroup G] (y : Fin q → G)
    (T : Finset (CollisionEvent q)) : Fin q → Fin q → G → Prop where
  | refl (i : Fin q) : collisionSubfamilyLabelReach y T i i 0
  | tail {i j k : Fin q} {acc step : G} :
      collisionSubfamilyLabelReach y T i j acc →
      collisionSubfamilyStepLabel y T j k step →
      collisionSubfamilyLabelReach y T i k (acc + step)

/-- Labelled reachability implies ordinary support-graph connectedness. -/
theorem collisionSubfamilyLabelReach_connected [AddGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {i j : Fin q} {label : G}
    (hreach : collisionSubfamilyLabelReach (G := G) (q := q) y T i j label) :
    collisionSubfamilyConnected (q := q) T i j := by
  induction hreach with
  | refl => exact collisionSubfamilyConnected_refl (q := q) T _
  | tail _hreach hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (collisionSubfamilyStepLabel_connected (G := G) (q := q) hstep)

/-- Every ordinary support-graph connection has some accumulated labelled
walk. -/
theorem collisionSubfamilyConnected_exists_labelReach [AddGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {i j : Fin q}
    (hij : collisionSubfamilyConnected (q := q) T i j) :
    ∃ label : G, collisionSubfamilyLabelReach (G := G) (q := q) y T i j label := by
  induction hij with
  | refl =>
      exact ⟨0, collisionSubfamilyLabelReach.refl (y := y) (T := T) i⟩
  | tail _hprev hstep ih =>
      rcases ih with ⟨acc, hacc⟩
      rcases collisionSubfamilyAdjacent_exists_stepLabel (G := G) (q := q)
          (y := y) hstep with ⟨step, hstepLabel⟩
      exact ⟨acc + step, collisionSubfamilyLabelReach.tail hacc hstepLabel⟩

/-- Concatenating labelled walks adds their accumulated labels. -/
theorem collisionSubfamilyLabelReach_append [AddGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)}
    {i j k : Fin q} {label₁ label₂ : G}
    (h₁ : collisionSubfamilyLabelReach (G := G) (q := q) y T i j label₁)
    (h₂ : collisionSubfamilyLabelReach (G := G) (q := q) y T j k label₂) :
    collisionSubfamilyLabelReach (G := G) (q := q) y T i k (label₁ + label₂) := by
  induction h₂ with
  | refl => simpa using h₁
  | tail _hprev hstep ih =>
      simpa [add_assoc] using collisionSubfamilyLabelReach.tail ih hstep

/-- Reversing a labelled walk negates its accumulated label. -/
theorem collisionSubfamilyLabelReach_reverse [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {i j : Fin q} {label : G}
    (hreach : collisionSubfamilyLabelReach (G := G) (q := q) y T i j label) :
    collisionSubfamilyLabelReach (G := G) (q := q) y T j i (-label) := by
  induction hreach with
  | refl => simpa using collisionSubfamilyLabelReach.refl (y := y) (T := T) i
  | tail _hprev hstep ih =>
      have hstep_rev := collisionSubfamilyStepLabel_symm (G := G) (q := q) hstep
      have hstep_reach := collisionSubfamilyLabelReach.tail
        (collisionSubfamilyLabelReach.refl (y := y) (T := T) _) hstep_rev
      have hcat := collisionSubfamilyLabelReach_append (G := G) (q := q) hstep_reach ih
      simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hcat

/-- Any solution to a labelled subfamily makes accumulated walk labels telescope
to endpoint differences. -/
theorem collisionSubfamilyLabelReach_equation [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {a : Fin q → G}
    (ha : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a)
    {i j : Fin q} {label : G}
    (hreach : collisionSubfamilyLabelReach (G := G) (q := q) y T i j label) :
    a i - a j = label := by
  induction hreach with
  | refl => simp
  | tail _hreach hstep ih =>
      have hs := collisionSubfamilyStepLabel_equation (G := G) (q := q)
        (y := y) (T := T) (a := a) ha hstep
      rw [← ih, ← hs]
      abel

/-- Closed-walk consistency for the labelled subfamily: every accumulated label
around a closed labelled walk is zero. -/
def collisionSubfamilyCycleConsistent [AddGroup G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) : Prop :=
  ∀ i label, collisionSubfamilyLabelReach (G := G) (q := q) y T i i label →
    label = 0

instance collisionSubfamilyCycleConsistentDecidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    Decidable (collisionSubfamilyCycleConsistent (G := G) (q := q) y T) :=
  Classical.propDecidable _

/-- Semantic satisfiability implies closed-walk label consistency. -/
theorem collisionSubfamilyCycleConsistent_of_consistent [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)}
    (hT : collisionSubfamilyConsistent (G := G) (q := q) y T) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y T := by
  rcases hT with ⟨a, ha⟩
  intro i label hreach
  have h := collisionSubfamilyLabelReach_equation (G := G) (q := q)
    (y := y) (T := T) (a := a) ha hreach
  simpa using h.symm

/-- Under closed-walk consistency, labelled paths with the same endpoints have
the same accumulated label. -/
theorem collisionSubfamilyLabelReach_label_unique [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)}
    (hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T)
    {i j : Fin q} {label₁ label₂ : G}
    (h₁ : collisionSubfamilyLabelReach (G := G) (q := q) y T i j label₁)
    (h₂ : collisionSubfamilyLabelReach (G := G) (q := q) y T i j label₂) :
    label₁ = label₂ := by
  have h₂rev := collisionSubfamilyLabelReach_reverse (G := G) (q := q) h₂
  have hclosed := collisionSubfamilyLabelReach_append (G := G) (q := q) h₁ h₂rev
  have hzero := hcyc i (label₁ + -label₂) hclosed
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg] using hzero

/-- Two solutions of one labelled collision equation have the same offset
between their endpoint values. -/
theorem collisionEventEquation_offset_eq [AddCommGroup G]
    {y : Fin q → G} {e : CollisionEvent q} {a b : Fin q → G}
    (ha : collisionEventEquation (G := G) (q := q) y e a)
    (hb : collisionEventEquation (G := G) (q := q) y e b) :
    a (collisionEventLeft e) - b (collisionEventLeft e) =
      a (collisionEventRight e) - b (collisionEventRight e) := by
  have hsame :
      a (collisionEventLeft e) - a (collisionEventRight e) =
        b (collisionEventLeft e) - b (collisionEventRight e) := ha.trans hb.symm
  rw [← sub_eq_zero] at hsame ⊢
  abel_nf at hsame ⊢
  exact hsame

/-- Two solutions of a collision-event subfamily have the same offset across
each support edge. -/
theorem collisionSubfamilyAdjacent_offset_eq [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {a b : Fin q → G} {i j : Fin q}
    (ha : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a)
    (hb : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e b)
    (hij : collisionSubfamilyAdjacent (q := q) T i j) :
    a i - b i = a j - b j := by
  rcases hij with ⟨e, heT, hends | hends⟩
  · rcases hends with ⟨hli, hrj⟩
    simpa [hli, hrj] using
      (collisionEventEquation_offset_eq (G := G) (q := q)
        (y := y) (e := e) (a := a) (b := b) (ha e heT) (hb e heT))
  · rcases hends with ⟨hlj, hri⟩
    symm
    simpa [hlj, hri] using
      (collisionEventEquation_offset_eq (G := G) (q := q)
        (y := y) (e := e) (a := a) (b := b) (ha e heT) (hb e heT))

/-- Two solutions of a collision-event subfamily differ by a componentwise
constant on every connected component of the support graph. -/
theorem collisionSubfamilyConnected_offset_eq [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {a b : Fin q → G} {i j : Fin q}
    (ha : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a)
    (hb : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e b)
    (hij : collisionSubfamilyConnected (q := q) T i j) :
    a i - b i = a j - b j := by
  induction hij with
  | refl => rfl
  | tail _hprev hstep ih =>
      exact ih.trans (collisionSubfamilyAdjacent_offset_eq (G := G) (q := q)
        (y := y) (T := T) (a := a) (b := b) ha hb hstep)

/-- A function on coordinates is constant on every support component of a
collision-event subfamily. -/
def collisionSubfamilyComponentConstant (T : Finset (CollisionEvent q))
    (z : Fin q → G) : Prop :=
  ∀ ⦃i j : Fin q⦄, collisionSubfamilyConnected (q := q) T i j → z i = z j

/-- The connected components of a collision-event subfamily, packaged as a
setoid on query coordinates. -/
def collisionSubfamilyConnectedSetoid (T : Finset (CollisionEvent q)) : Setoid (Fin q) where
  r := collisionSubfamilyConnected (q := q) T
  iseqv := ⟨collisionSubfamilyConnected_refl (q := q) T,
    fun {_ _} hij => collisionSubfamilyConnected_symm (q := q) T hij,
    fun {_ _ _} hij hjk => Relation.ReflTransGen.trans hij hjk⟩

/-- The finite quotient of coordinates by connected components of a
collision-event subfamily. -/
abbrev collisionSubfamilyComponent (T : Finset (CollisionEvent q)) :=
  Quotient (collisionSubfamilyConnectedSetoid (q := q) T)

instance collisionSubfamilyConnectedSetoidDecidableRel (T : Finset (CollisionEvent q)) :
    DecidableRel ((collisionSubfamilyConnectedSetoid (q := q) T).r) :=
  fun _ _ => Classical.propDecidable _

instance collisionSubfamilyComponentFintype (T : Finset (CollisionEvent q)) :
    Fintype (collisionSubfamilyComponent (q := q) T) := by
  unfold collisionSubfamilyComponent
  infer_instance

instance collisionSubfamilyComponentConstantDecidablePred (T : Finset (CollisionEvent q)) :
    DecidablePred (fun z : Fin q → G =>
      collisionSubfamilyComponentConstant (q := q) T z) :=
  fun _ => Classical.propDecidable _

/-- Number of connected components in the support graph of a collision-event
subfamily. -/
def collisionSubfamilyComponentCount (T : Finset (CollisionEvent q)) : Nat :=
  Fintype.card (collisionSubfamilyComponent (q := q) T)

/-- The natural quotient map from components of a smaller support graph to
components of a larger support graph. -/
def collisionSubfamilyComponentMap {S T : Finset (CollisionEvent q)} (hST : S ⊆ T) :
    collisionSubfamilyComponent (q := q) S → collisionSubfamilyComponent (q := q) T :=
  fun c =>
    Quotient.liftOn c
      (fun i => (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
        collisionSubfamilyComponent (q := q) T))
      (by
        intro i j hij
        apply Quotient.sound
        exact collisionSubfamilyConnected_mono (q := q) hST
          (by simpa [collisionSubfamilyConnectedSetoid] using hij))

/-- The natural component map induced by enlarging support is surjective. -/
theorem collisionSubfamilyComponentMap_surjective {S T : Finset (CollisionEvent q)}
    (hST : S ⊆ T) :
    Function.Surjective (collisionSubfamilyComponentMap (q := q) hST) := by
  intro c
  induction c using Quotient.inductionOn with
  | h i =>
      exact ⟨Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) S) i, rfl⟩

/-- Enlarging a collision-event subfamily can only merge support components. -/
theorem collisionSubfamilyComponentCount_anti {S T : Finset (CollisionEvent q)}
    (hST : S ⊆ T) :
    collisionSubfamilyComponentCount (q := q) T ≤
      collisionSubfamilyComponentCount (q := q) S := by
  simpa [collisionSubfamilyComponentCount] using
    Fintype.card_le_of_surjective
      (collisionSubfamilyComponentMap (q := q) hST)
      (collisionSubfamilyComponentMap_surjective (q := q) hST)

/-- If enlarging a support graph does not change the number of components, then
every connection in the larger graph was already present in the smaller graph. -/
theorem collisionSubfamilyConnected_of_connected_of_componentCount_eq
    {S T : Finset (CollisionEvent q)} (hST : S ⊆ T)
    (hcount : collisionSubfamilyComponentCount (q := q) S =
      collisionSubfamilyComponentCount (q := q) T)
    {i j : Fin q} (hij : collisionSubfamilyConnected (q := q) T i j) :
    collisionSubfamilyConnected (q := q) S i j := by
  let π := collisionSubfamilyComponentMap (q := q) hST
  have hsurj : Function.Surjective π :=
    collisionSubfamilyComponentMap_surjective (q := q) hST
  have hcard :
      Fintype.card (collisionSubfamilyComponent (q := q) S) =
        Fintype.card (collisionSubfamilyComponent (q := q) T) := by
    simpa [collisionSubfamilyComponentCount] using hcount
  have hbij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hsurj, hcard⟩
  have himage :
      π (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) S) i) =
        π (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) S) j) := by
    apply Quotient.sound
    simpa [collisionSubfamilyConnectedSetoid] using hij
  have hpre := hbij.1 himage
  simpa [collisionSubfamilyConnectedSetoid] using Quotient.exact hpre

/-- Graphic rank of the support graph of a collision-event subfamily. -/
def collisionSubfamilyGraphicRank (T : Finset (CollisionEvent q)) : Nat :=
  q - collisionSubfamilyComponentCount (q := q) T

/-- Graphic rank, packaged as a finite classifier. -/
def collisionSubfamilyGraphicRankFin (T : Finset (CollisionEvent q)) : Fin (q + 1) :=
  ⟨collisionSubfamilyGraphicRank (q := q) T,
    Nat.lt_succ_of_le (Nat.sub_le q (collisionSubfamilyComponentCount (q := q) T))⟩

/-- The finite rank classifier value corresponding to graphic rank one. -/
def collisionSubfamilyGraphicRankOneFin {q : Nat} (hq : 0 < q) : Fin (q + 1) :=
  ⟨1, Nat.succ_lt_succ hq⟩

/-- A collision-event subfamily has at most one support component per query
coordinate. -/
theorem collisionSubfamilyComponentCount_le_query (T : Finset (CollisionEvent q)) :
    collisionSubfamilyComponentCount (q := q) T ≤ q := by
  have hsurj : Function.Surjective
      (fun i : Fin q => (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
        collisionSubfamilyComponent (q := q) T)) := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact ⟨i, rfl⟩
  simpa [collisionSubfamilyComponentCount, Fintype.card_fin] using
    Fintype.card_le_of_surjective
      (fun i : Fin q => (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
        collisionSubfamilyComponent (q := q) T)) hsurj

/-- The component count is `q` minus the graphic rank. -/
theorem collisionSubfamilyComponentCount_eq_query_sub_graphicRank
    (T : Finset (CollisionEvent q)) :
    collisionSubfamilyComponentCount (q := q) T =
      q - collisionSubfamilyGraphicRank (q := q) T := by
  unfold collisionSubfamilyGraphicRank
  have hle := collisionSubfamilyComponentCount_le_query (q := q) T
  omega

/-- Enlarging a collision-event subfamily can only increase graphic rank. -/
theorem collisionSubfamilyGraphicRank_mono {S T : Finset (CollisionEvent q)}
    (hST : S ⊆ T) :
    collisionSubfamilyGraphicRank (q := q) S ≤
      collisionSubfamilyGraphicRank (q := q) T := by
  unfold collisionSubfamilyGraphicRank
  have hS := collisionSubfamilyComponentCount_le_query (q := q) S
  have hT := collisionSubfamilyComponentCount_le_query (q := q) T
  have hanti := collisionSubfamilyComponentCount_anti (q := q) hST
  omega

/-- Every subfamily of a graphic-rank-one collision-event family has graphic
rank at most one. -/
theorem collisionSubfamilyGraphicRank_le_one_of_subset_rank_one
    {S T : Finset (CollisionEvent q)} (hST : S ⊆ T)
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1) :
    collisionSubfamilyGraphicRank (q := q) S ≤ 1 := by
  exact (collisionSubfamilyGraphicRank_mono (q := q) hST).trans_eq hrank

/-- With no selected collision events, support-graph connectivity is equality. -/
theorem collisionSubfamilyConnected_empty_iff (i j : Fin q) :
    collisionSubfamilyConnected (q := q) (∅ : Finset (CollisionEvent q)) i j ↔ i = j := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _hprev hadj _ih =>
        rcases hadj with ⟨_e, he, _hends⟩
        simp at he
  · intro h
    subst h
    exact collisionSubfamilyConnected_refl (q := q) ∅ i

/-- The empty collision-event subfamily has one connected component per query
coordinate. -/
theorem collisionSubfamilyComponentCount_empty :
    collisionSubfamilyComponentCount (q := q) (∅ : Finset (CollisionEvent q)) = q := by
  let π : Fin q → collisionSubfamilyComponent (q := q) (∅ : Finset (CollisionEvent q)) :=
    fun i =>
      Quotient.mk
        (collisionSubfamilyConnectedSetoid (q := q) (∅ : Finset (CollisionEvent q))) i
  have hsurj : Function.Surjective π := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact ⟨i, rfl⟩
  have hinj : Function.Injective π := by
    intro i j h
    exact (collisionSubfamilyConnected_empty_iff (q := q) i j).mp (Quotient.exact h)
  have hcard := Fintype.card_congr (Equiv.ofBijective π ⟨hinj, hsurj⟩)
  simpa [π, collisionSubfamilyComponentCount, Fintype.card_fin] using hcard.symm

/-- The empty collision-event subfamily has graphic rank zero. -/
theorem collisionSubfamilyGraphicRank_empty :
    collisionSubfamilyGraphicRank (q := q) (∅ : Finset (CollisionEvent q)) = 0 := by
  simp [collisionSubfamilyGraphicRank, collisionSubfamilyComponentCount_empty]

/-- Any nonempty collision-event subfamily identifies two distinct query
coordinates, so its support graph has strictly fewer than `q` components. -/
theorem collisionSubfamilyComponentCount_lt_query_of_nonempty
    {T : Finset (CollisionEvent q)} (hT : T.Nonempty) :
    collisionSubfamilyComponentCount (q := q) T < q := by
  rcases hT with ⟨e, heT⟩
  let π : Fin q → collisionSubfamilyComponent (q := q) T :=
    fun i => Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i
  have hsurj : Function.Surjective π := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact ⟨i, rfl⟩
  have hnotinj : ¬ Function.Injective π := by
    intro hinj
    have hqeq : π (collisionEventLeft e) = π (collisionEventRight e) := by
      exact Quotient.sound (by
        simpa [collisionSubfamilyConnectedSetoid] using
          (Relation.ReflTransGen.single
            (r := collisionSubfamilyAdjacent (q := q) T)
            ⟨e, heT, Or.inl ⟨rfl, rfl⟩⟩))
    have hend : collisionEventLeft e = collisionEventRight e := hinj hqeq
    exact (ne_of_lt (collisionEventLeft_lt_right (q := q) e)) hend
  simpa [π, collisionSubfamilyComponentCount, Fintype.card_fin] using
    Fintype.card_lt_of_surjective_not_injective π hsurj hnotinj

/-- A collision-event subfamily has graphic rank zero only when it is empty. -/
theorem collisionSubfamily_eq_empty_of_graphicRank_eq_zero
    {T : Finset (CollisionEvent q)}
    (hT : collisionSubfamilyGraphicRank (q := q) T = 0) : T = ∅ := by
  by_contra hne
  have hnon : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hlt := collisionSubfamilyComponentCount_lt_query_of_nonempty (q := q) hnon
  have hcomp := collisionSubfamilyComponentCount_eq_query_sub_graphicRank (q := q) T
  rw [hT, Nat.sub_zero] at hcomp
  omega

/-- Every nonempty collision-event subfamily has positive graphic rank. -/
theorem collisionSubfamilyGraphicRank_pos_of_nonempty
    {T : Finset (CollisionEvent q)} (hT : T.Nonempty) :
    0 < collisionSubfamilyGraphicRank (q := q) T := by
  unfold collisionSubfamilyGraphicRank
  have hlt := collisionSubfamilyComponentCount_lt_query_of_nonempty (q := q) hT
  omega

/-- Every nonempty subfamily of a graphic-rank-one collision-event family also
has graphic rank one. -/
theorem collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_rank_one
    {S T : Finset (CollisionEvent q)} (hne : S.Nonempty) (hST : S ⊆ T)
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1) :
    collisionSubfamilyGraphicRank (q := q) S = 1 := by
  have hpos := collisionSubfamilyGraphicRank_pos_of_nonempty (q := q) hne
  have hle := collisionSubfamilyGraphicRank_le_one_of_subset_rank_one (q := q) hST hrank
  omega

/-- A singleton collision-event subfamily has positive graphic rank. -/
theorem collisionSubfamilyGraphicRank_singleton_pos (e : CollisionEvent q) :
    0 < collisionSubfamilyGraphicRank (q := q) ({e} : Finset (CollisionEvent q)) :=
  collisionSubfamilyGraphicRank_pos_of_nonempty (q := q) (Finset.singleton_nonempty e)

/-- Representative of a component in a singleton support graph: the right
endpoint is folded into the left endpoint, and all other coordinates remain
fixed. -/
def collisionSubfamilySingletonComponentRep (e : CollisionEvent q)
    (i : Fin q) : {j : Fin q // j ≠ collisionEventRight e} :=
  if h : i = collisionEventRight e then
    ⟨collisionEventLeft e, by
      intro hlr
      exact (ne_of_lt (collisionEventLeft_lt_right (q := q) e)) hlr⟩
  else
    ⟨i, h⟩

/-- Adjacent coordinates in a singleton support graph have the same folded
component representative. -/
theorem collisionSubfamilySingletonAdjacent_rep_eq
    (e : CollisionEvent q) {i j : Fin q}
    (hij : collisionSubfamilyAdjacent (q := q) ({e} : Finset (CollisionEvent q)) i j) :
    collisionSubfamilySingletonComponentRep (q := q) e i =
      collisionSubfamilySingletonComponentRep (q := q) e j := by
  rcases hij with ⟨e', he', hends | hends⟩
  · have heq : e' = e := by simpa using he'
    subst e'
    rcases hends with ⟨hi, hj⟩
    subst i
    subst j
    unfold collisionSubfamilySingletonComponentRep
    simp [ne_of_lt (collisionEventLeft_lt_right (q := q) e)]
  · have heq : e' = e := by simpa using he'
    subst e'
    rcases hends with ⟨hi, hj⟩
    subst j
    subst i
    unfold collisionSubfamilySingletonComponentRep
    simp [ne_of_lt (collisionEventLeft_lt_right (q := q) e)]

/-- Connected coordinates in a singleton support graph have the same folded
component representative. -/
theorem collisionSubfamilySingletonConnected_rep_eq
    (e : CollisionEvent q) {i j : Fin q}
    (hij : collisionSubfamilyConnected (q := q) ({e} : Finset (CollisionEvent q)) i j) :
    collisionSubfamilySingletonComponentRep (q := q) e i =
      collisionSubfamilySingletonComponentRep (q := q) e j := by
  induction hij with
  | refl => rfl
  | tail _hprev hadj ih =>
      exact ih.trans (collisionSubfamilySingletonAdjacent_rep_eq (q := q) e hadj)

/-- Connected components of a singleton support graph are equivalent to all
coordinates except the right endpoint of the selected edge. -/
def collisionSubfamilySingletonComponentEquiv (e : CollisionEvent q) :
    collisionSubfamilyComponent (q := q) ({e} : Finset (CollisionEvent q)) ≃
      {j : Fin q // j ≠ collisionEventRight e} where
  toFun c :=
    Quotient.liftOn c (collisionSubfamilySingletonComponentRep (q := q) e) (by
      intro i j hij
      exact collisionSubfamilySingletonConnected_rep_eq (q := q) e
        (by simpa [collisionSubfamilyConnectedSetoid] using hij))
  invFun j :=
    Quotient.mk (collisionSubfamilyConnectedSetoid (q := q)
      ({e} : Finset (CollisionEvent q))) j.1
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h i =>
        dsimp
        by_cases hi : i = collisionEventRight e
        · unfold collisionSubfamilySingletonComponentRep
          rw [dif_pos hi]
          apply Quotient.sound
          rw [hi]
          exact Relation.ReflTransGen.single
            (r := collisionSubfamilyAdjacent (q := q) ({e} : Finset (CollisionEvent q)))
            ⟨e, by simp, Or.inl ⟨rfl, rfl⟩⟩
        · unfold collisionSubfamilySingletonComponentRep
          rw [dif_neg hi]
  right_inv j := by
    ext
    dsimp
    unfold collisionSubfamilySingletonComponentRep
    have hj : ¬ (j.1 = collisionEventRight e) := j.2
    rw [dif_neg hj]

/-- The folded representative completely characterizes connectivity in a
singleton support graph. -/
theorem collisionSubfamilySingletonConnected_iff_rep_eq
    (e : CollisionEvent q) {i j : Fin q} :
    collisionSubfamilyConnected (q := q) ({e} : Finset (CollisionEvent q)) i j ↔
      collisionSubfamilySingletonComponentRep (q := q) e i =
        collisionSubfamilySingletonComponentRep (q := q) e j := by
  constructor
  · exact collisionSubfamilySingletonConnected_rep_eq (q := q) e
  · intro hrep
    have hquot :
        (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q)
          ({e} : Finset (CollisionEvent q))) i :
          collisionSubfamilyComponent (q := q) ({e} : Finset (CollisionEvent q))) =
        Quotient.mk (collisionSubfamilyConnectedSetoid (q := q)
          ({e} : Finset (CollisionEvent q))) j := by
      apply (collisionSubfamilySingletonComponentEquiv (q := q) e).injective
      change collisionSubfamilySingletonComponentRep (q := q) e i =
        collisionSubfamilySingletonComponentRep (q := q) e j
      exact hrep
    simpa [collisionSubfamilyConnectedSetoid] using Quotient.exact hquot

/-- A singleton collision-event subfamily has exactly `q - 1` connected
components. -/
theorem collisionSubfamilyComponentCount_singleton (e : CollisionEvent q) :
    collisionSubfamilyComponentCount (q := q) ({e} : Finset (CollisionEvent q)) = q - 1 := by
  rw [collisionSubfamilyComponentCount]
  rw [Fintype.card_congr (collisionSubfamilySingletonComponentEquiv (q := q) e)]
  rw [Fintype.card_subtype_compl (p := fun i : Fin q => i = collisionEventRight e)]
  simp

/-- A singleton collision-event subfamily has graphic rank exactly one. -/
theorem collisionSubfamilyGraphicRank_singleton (e : CollisionEvent q) :
    collisionSubfamilyGraphicRank (q := q) ({e} : Finset (CollisionEvent q)) = 1 := by
  unfold collisionSubfamilyGraphicRank
  rw [collisionSubfamilyComponentCount_singleton]
  have hqpos : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (collisionEventRight e).isLt
  omega

/-- All events in a collision-event subfamily have the same endpoints as `e`. -/
def collisionSubfamilySameEndpoints (e : CollisionEvent q)
    (T : Finset (CollisionEvent q)) : Prop :=
  ∀ e' ∈ T,
    collisionEventLeft e' = collisionEventLeft e ∧
      collisionEventRight e' = collisionEventRight e

/-- Adjacent coordinates in a same-endpoints support graph have the same folded
component representative. -/
theorem collisionSubfamilySameEndpointsAdjacent_rep_eq
    (e : CollisionEvent q) {T : Finset (CollisionEvent q)}
    (hsame : collisionSubfamilySameEndpoints (q := q) e T) {i j : Fin q}
    (hij : collisionSubfamilyAdjacent (q := q) T i j) :
    collisionSubfamilySingletonComponentRep (q := q) e i =
      collisionSubfamilySingletonComponentRep (q := q) e j := by
  rcases hij with ⟨e', heT, hends | hends⟩
  · rcases hsame e' heT with ⟨hl, hr⟩
    rcases hends with ⟨hi, hj⟩
    subst i
    subst j
    rw [hl, hr]
    unfold collisionSubfamilySingletonComponentRep
    simp [ne_of_lt (collisionEventLeft_lt_right (q := q) e)]
  · rcases hsame e' heT with ⟨hl, hr⟩
    rcases hends with ⟨hi, hj⟩
    subst j
    subst i
    rw [hl, hr]
    unfold collisionSubfamilySingletonComponentRep
    simp [ne_of_lt (collisionEventLeft_lt_right (q := q) e)]

/-- Connected coordinates in a same-endpoints support graph have the same folded
component representative. -/
theorem collisionSubfamilySameEndpointsConnected_rep_eq
    (e : CollisionEvent q) {T : Finset (CollisionEvent q)}
    (hsame : collisionSubfamilySameEndpoints (q := q) e T) {i j : Fin q}
    (hij : collisionSubfamilyConnected (q := q) T i j) :
    collisionSubfamilySingletonComponentRep (q := q) e i =
      collisionSubfamilySingletonComponentRep (q := q) e j := by
  induction hij with
  | refl => rfl
  | tail _hprev hadj ih =>
      exact ih.trans (collisionSubfamilySameEndpointsAdjacent_rep_eq (q := q) e hsame hadj)

/-- Connected components of a nonempty same-endpoints support graph are
equivalent to all coordinates except the common right endpoint. -/
def collisionSubfamilySameEndpointsComponentEquiv
    (e : CollisionEvent q) {T : Finset (CollisionEvent q)}
    (hne : T.Nonempty) (hsame : collisionSubfamilySameEndpoints (q := q) e T) :
    collisionSubfamilyComponent (q := q) T ≃
      {j : Fin q // j ≠ collisionEventRight e} where
  toFun c :=
    Quotient.liftOn c (collisionSubfamilySingletonComponentRep (q := q) e) (by
      intro i j hij
      exact collisionSubfamilySameEndpointsConnected_rep_eq (q := q) e hsame
        (by simpa [collisionSubfamilyConnectedSetoid] using hij))
  invFun j :=
    Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) j.1
  left_inv c := by
    rcases hne with ⟨e0, he0T⟩
    have h0 := hsame e0 he0T
    induction c using Quotient.inductionOn with
    | h i =>
        dsimp
        by_cases hi : i = collisionEventRight e
        · unfold collisionSubfamilySingletonComponentRep
          rw [dif_pos hi]
          apply Quotient.sound
          rw [hi]
          exact Relation.ReflTransGen.single
            (r := collisionSubfamilyAdjacent (q := q) T)
            ⟨e0, he0T, Or.inl ⟨h0.1, h0.2⟩⟩
        · unfold collisionSubfamilySingletonComponentRep
          rw [dif_neg hi]
  right_inv j := by
    ext
    dsimp
    unfold collisionSubfamilySingletonComponentRep
    have hj : ¬ (j.1 = collisionEventRight e) := j.2
    rw [dif_neg hj]

/-- A nonempty same-endpoints collision-event subfamily has exactly `q - 1`
connected components. -/
theorem collisionSubfamilyComponentCount_eq_of_sameEndpoints
    (e : CollisionEvent q) {T : Finset (CollisionEvent q)}
    (hne : T.Nonempty) (hsame : collisionSubfamilySameEndpoints (q := q) e T) :
    collisionSubfamilyComponentCount (q := q) T = q - 1 := by
  rw [collisionSubfamilyComponentCount]
  rw [Fintype.card_congr
    (collisionSubfamilySameEndpointsComponentEquiv (q := q) e hne hsame)]
  rw [Fintype.card_subtype_compl (p := fun i : Fin q => i = collisionEventRight e)]
  simp

/-- A nonempty same-endpoints collision-event subfamily has graphic rank one. -/
theorem collisionSubfamilyGraphicRank_eq_one_of_sameEndpoints
    (e : CollisionEvent q) {T : Finset (CollisionEvent q)}
    (hne : T.Nonempty) (hsame : collisionSubfamilySameEndpoints (q := q) e T) :
    collisionSubfamilyGraphicRank (q := q) T = 1 := by
  unfold collisionSubfamilyGraphicRank
  rw [collisionSubfamilyComponentCount_eq_of_sameEndpoints (q := q) e hne hsame]
  have hqpos : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (collisionEventRight e).isLt
  omega

/-- Component-constant coordinate functions are exactly functions on the
component quotient. -/
def collisionSubfamilyComponentConstantEquivQuotientFunction
    (T : Finset (CollisionEvent q)) :
    { z : Fin q → G // collisionSubfamilyComponentConstant (q := q) T z } ≃
      (collisionSubfamilyComponent (q := q) T → G) where
  toFun z := fun c =>
    Quotient.liftOn c z.1 (by
      intro i j hij
      exact z.2 (by simpa [collisionSubfamilyConnectedSetoid] using hij))
  invFun f :=
    ⟨fun i => f ⟦i⟧, by
      intro i j hij
      exact congrArg f
        (Quotient.sound (by simpa [collisionSubfamilyConnectedSetoid] using hij))⟩
  left_inv z := by
    ext i
    rfl
  right_inv f := by
    funext c
    induction c using Quotient.inductionOn with
    | h i => rfl

/-- The number of component-constant offsets is one free `G`-value per support
component. -/
theorem card_collisionSubfamilyComponentConstant [Fintype G]
    (T : Finset (CollisionEvent q)) :
    Fintype.card { z : Fin q → G //
        collisionSubfamilyComponentConstant (q := q) T z } =
      (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T := by
  classical
  rw [Fintype.card_congr
    (collisionSubfamilyComponentConstantEquivQuotientFunction (G := G) (q := q) T)]
  rw [Fintype.card_fun]
  rfl

instance collisionSubfamilyEquationsDecidablePred [AddGroup G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    DecidablePred (fun a : Fin q → G =>
      ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a) :=
  fun _ => Classical.propDecidable _

/-- Adjacent coordinates are connected. -/
theorem collisionSubfamilyAdjacent_connected
    {T : Finset (CollisionEvent q)} {i j : Fin q}
    (hij : collisionSubfamilyAdjacent (q := q) T i j) :
    collisionSubfamilyConnected (q := q) T i j :=
  Relation.ReflTransGen.single hij

/-- The endpoints of an event in the subfamily are connected in the support
graph. -/
theorem collisionSubfamilyEvent_connected
    {T : Finset (CollisionEvent q)} {e : CollisionEvent q} (heT : e ∈ T) :
    collisionSubfamilyConnected (q := q) T
      (collisionEventLeft e) (collisionEventRight e) :=
  Relation.ReflTransGen.single ⟨e, heT, Or.inl ⟨rfl, rfl⟩⟩

/-- In a graphic-rank-one support family, the endpoints of any selected event
are already connected in the singleton support graph of any other selected
event. -/
theorem collisionSubfamilyEvent_connected_in_singleton_of_rank_one
    {T : Finset (CollisionEvent q)} (hrank : collisionSubfamilyGraphicRank (q := q) T = 1)
    {e₁ e₂ : CollisionEvent q} (he₁ : e₁ ∈ T) (he₂ : e₂ ∈ T) :
    collisionSubfamilyConnected (q := q) ({e₁} : Finset (CollisionEvent q))
      (collisionEventLeft e₂) (collisionEventRight e₂) := by
  have hST : ({e₁} : Finset (CollisionEvent q)) ⊆ T := by
    intro e he
    have heq : e = e₁ := by simpa using he
    subst e
    exact he₁
  have hcount : collisionSubfamilyComponentCount (q := q) ({e₁} : Finset (CollisionEvent q)) =
      collisionSubfamilyComponentCount (q := q) T := by
    rw [collisionSubfamilyComponentCount_eq_query_sub_graphicRank (q := q)
      ({e₁} : Finset (CollisionEvent q))]
    rw [collisionSubfamilyComponentCount_eq_query_sub_graphicRank (q := q) T]
    rw [collisionSubfamilyGraphicRank_singleton, hrank]
  exact collisionSubfamilyConnected_of_connected_of_componentCount_eq (q := q)
    hST hcount (collisionSubfamilyEvent_connected (q := q) he₂)

/-- In a graphic-rank-one support family, endpoints of selected events fold to
the same representative in any other selected singleton support. -/
theorem collisionSubfamilySingletonRep_eq_of_mem_rank_one
    {T : Finset (CollisionEvent q)} (hrank : collisionSubfamilyGraphicRank (q := q) T = 1)
    {e₁ e₂ : CollisionEvent q} (he₁ : e₁ ∈ T) (he₂ : e₂ ∈ T) :
    collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventLeft e₂) =
      collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventRight e₂) := by
  exact (collisionSubfamilySingletonConnected_iff_rep_eq (q := q) e₁).mp
    (collisionSubfamilyEvent_connected_in_singleton_of_rank_one (q := q) hrank he₁ he₂)

/-- If the two endpoints of an event fold to the same representative in a
singleton support graph, then the two events have the same endpoint pair. -/
theorem collisionEvent_endpoints_eq_of_singletonRep_eq
    (e₁ e₂ : CollisionEvent q)
    (hrep : collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventLeft e₂) =
      collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventRight e₂)) :
    collisionEventLeft e₂ = collisionEventLeft e₁ ∧
      collisionEventRight e₂ = collisionEventRight e₁ := by
  have hval :
      (collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventLeft e₂)).1 =
        (collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventRight e₂)).1 :=
    congrArg Subtype.val hrep
  unfold collisionSubfamilySingletonComponentRep at hval
  by_cases hl : collisionEventLeft e₂ = collisionEventRight e₁
  · rw [dif_pos hl] at hval
    by_cases hr : collisionEventRight e₂ = collisionEventRight e₁
    · have hbad : collisionEventLeft e₂ = collisionEventRight e₂ := by rw [hl, hr]
      exact False.elim ((ne_of_lt (collisionEventLeft_lt_right (q := q) e₂)) hbad)
    · rw [dif_neg hr] at hval
      have hleft : collisionEventLeft e₁ = collisionEventRight e₂ := hval
      have hlt₁ := collisionEventLeft_lt_right (q := q) e₁
      have hlt₂ := collisionEventLeft_lt_right (q := q) e₂
      rw [hleft] at hlt₁
      rw [hl] at hlt₂
      omega
  · rw [dif_neg hl] at hval
    by_cases hr : collisionEventRight e₂ = collisionEventRight e₁
    · rw [dif_pos hr] at hval
      exact ⟨hval, hr⟩
    · rw [dif_neg hr] at hval
      exact False.elim ((ne_of_lt (collisionEventLeft_lt_right (q := q) e₂)) hval)

/-- In a graphic-rank-one support family, all selected events have the same
endpoints as any fixed selected event. -/
theorem collisionEvent_endpoints_eq_of_mem_graphicRank_eq_one
    {T : Finset (CollisionEvent q)} (hrank : collisionSubfamilyGraphicRank (q := q) T = 1)
    {e₁ e₂ : CollisionEvent q} (he₁ : e₁ ∈ T) (he₂ : e₂ ∈ T) :
    collisionEventLeft e₂ = collisionEventLeft e₁ ∧
      collisionEventRight e₂ = collisionEventRight e₁ :=
  collisionEvent_endpoints_eq_of_singletonRep_eq (q := q) e₁ e₂
    (collisionSubfamilySingletonRep_eq_of_mem_rank_one (q := q) hrank he₁ he₂)

/-- A graphic-rank-one support family is same-endpoint relative to any selected
event. -/
theorem collisionSubfamilySameEndpoints_of_graphicRank_eq_one
    {T : Finset (CollisionEvent q)} (hrank : collisionSubfamilyGraphicRank (q := q) T = 1)
    {e : CollisionEvent q} (he : e ∈ T) :
    collisionSubfamilySameEndpoints (q := q) e T := by
  intro e' he'
  exact collisionEvent_endpoints_eq_of_mem_graphicRank_eq_one (q := q) hrank he he'

/-- Equality of event endpoints implies equality of the underlying query pair. -/
theorem collisionEvent_pairIndex_eq_of_endpoints_eq
    {e₁ e₂ : CollisionEvent q}
    (hl : collisionEventLeft e₂ = collisionEventLeft e₁)
    (hr : collisionEventRight e₂ = collisionEventRight e₁) :
    e₂.1 = e₁.1 := by
  apply Subtype.ext
  exact Prod.ext hl hr

/-- A graphic-rank-one support family is contained in the pair-local event set
of any selected event. -/
theorem collisionSubfamily_subset_collisionPairEvents_of_graphicRank_eq_one
    {T : Finset (CollisionEvent q)} (hrank : collisionSubfamilyGraphicRank (q := q) T = 1)
    {e : CollisionEvent q} (he : e ∈ T) :
    T ⊆ collisionPairEvents (q := q) e.1 := by
  intro e' he'
  have hends := collisionEvent_endpoints_eq_of_mem_graphicRank_eq_one (q := q) hrank he he'
  have hp : e'.1 = e.1 :=
    collisionEvent_pairIndex_eq_of_endpoints_eq (q := q) hends.1 hends.2
  rcases e' with ⟨p', kind⟩
  dsimp at hp
  subst p'
  cases kind <;> simp [collisionPairEvents]

/-- Chosen representative of the connected component containing a coordinate. -/
def collisionSubfamilyRoot (T : Finset (CollisionEvent q)) (i : Fin q) : Fin q :=
  Quotient.out (⟦i⟧ : collisionSubfamilyComponent (q := q) T)

/-- The chosen component representative is connected to the coordinate. -/
theorem collisionSubfamilyRoot_connected (T : Finset (CollisionEvent q)) (i : Fin q) :
    collisionSubfamilyConnected (q := q) T (collisionSubfamilyRoot (q := q) T i) i := by
  have hq := Quotient.out_eq' (⟦i⟧ : collisionSubfamilyComponent (q := q) T)
  exact Quotient.exact hq

/-- The chosen accumulated label from the component representative to a
coordinate.  Closed-walk consistency later proves this choice is independent of
the chosen labelled path. -/
def collisionSubfamilyPathLabel [AddGroup G] (y : Fin q → G)
    (T : Finset (CollisionEvent q)) (i : Fin q) : G :=
  Classical.choose (collisionSubfamilyConnected_exists_labelReach (G := G) (q := q)
    (y := y) (T := T) (collisionSubfamilyRoot_connected (q := q) T i))

/-- The chosen path label is realized by a labelled walk from the component
representative. -/
theorem collisionSubfamilyPathLabel_spec [AddGroup G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) (i : Fin q) :
    collisionSubfamilyLabelReach (G := G) (q := q) y T
      (collisionSubfamilyRoot (q := q) T i) i
      (collisionSubfamilyPathLabel (G := G) (q := q) y T i) :=
  Classical.choose_spec (collisionSubfamilyConnected_exists_labelReach (G := G) (q := q)
    (y := y) (T := T) (collisionSubfamilyRoot_connected (q := q) T i))

/-- The potential assignment induced by closed-walk consistency. -/
def collisionSubfamilyPotential [AddGroup G] (y : Fin q → G)
    (T : Finset (CollisionEvent q)) (i : Fin q) : G :=
  -collisionSubfamilyPathLabel (G := G) (q := q) y T i

/-- Closed-walk label consistency constructs a satisfying assignment. -/
theorem collisionSubfamilyConsistent_of_cycleConsistent [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)}
    (hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T) :
    collisionSubfamilyConsistent (G := G) (q := q) y T := by
  refine ⟨collisionSubfamilyPotential (G := G) (q := q) y T, ?_⟩
  intro e heT
  unfold collisionEventEquation collisionSubfamilyPotential
  let l := collisionEventLeft e
  let r := collisionEventRight e
  let lab := collisionEventLabel y e
  let ρl := collisionSubfamilyRoot (q := q) T l
  let ρr := collisionSubfamilyRoot (q := q) T r
  let α := collisionSubfamilyPathLabel (G := G) (q := q) y T l
  let β := collisionSubfamilyPathLabel (G := G) (q := q) y T r
  have hroot_eq : ρl = ρr := by
    dsimp [ρl, ρr, collisionSubfamilyRoot]
    apply congrArg Quotient.out
    exact Quotient.sound (collisionSubfamilyEvent_connected (q := q) (T := T) heT)
  have hα : collisionSubfamilyLabelReach (G := G) (q := q) y T ρl l α := by
    dsimp [ρl, α]
    exact collisionSubfamilyPathLabel_spec (G := G) (q := q) y T l
  have hβ : collisionSubfamilyLabelReach (G := G) (q := q) y T ρr r β := by
    dsimp [ρr, β]
    exact collisionSubfamilyPathLabel_spec (G := G) (q := q) y T r
  have hβ' : collisionSubfamilyLabelReach (G := G) (q := q) y T ρl r β := by
    simpa [hroot_eq] using hβ
  have hstep : collisionSubfamilyStepLabel (G := G) (q := q) y T l r lab :=
    ⟨e, heT, Or.inl ⟨rfl, rfl, rfl⟩⟩
  have hAlphaLab : collisionSubfamilyLabelReach (G := G) (q := q) y T ρl r (α + lab) :=
    collisionSubfamilyLabelReach.tail hα hstep
  have huniq : α + lab = β :=
    collisionSubfamilyLabelReach_label_unique (G := G) (q := q) hcyc hAlphaLab hβ'
  change -α - -β = lab
  rw [← huniq]
  abel

/-- Semantic consistency is equivalent to closed-walk label consistency. -/
theorem collisionSubfamilyConsistent_iff_cycleConsistent [AddCommGroup G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    collisionSubfamilyConsistent (G := G) (q := q) y T ↔
      collisionSubfamilyCycleConsistent (G := G) (q := q) y T :=
  ⟨collisionSubfamilyCycleConsistent_of_consistent,
    collisionSubfamilyConsistent_of_cycleConsistent⟩

/-- The difference of two solutions is constant on support components. -/
theorem collisionSubfamilyComponentConstant_of_solution_offsets [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {a b : Fin q → G}
    (ha : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a)
    (hb : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e b) :
    collisionSubfamilyComponentConstant (q := q) T (fun i => a i - b i) := by
  intro _i _j hij
  exact collisionSubfamilyConnected_offset_eq (G := G) (q := q)
    (y := y) (T := T) (a := a) (b := b) ha hb hij

/-- Adding a component-constant offset to one solution preserves one labelled
collision equation from the subfamily. -/
theorem collisionEventEquation_add_componentConstant [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {base z : Fin q → G}
    {e : CollisionEvent q}
    (hbase : collisionEventEquation (G := G) (q := q) y e base)
    (heT : e ∈ T)
    (hz : collisionSubfamilyComponentConstant (q := q) T z) :
    collisionEventEquation (G := G) (q := q) y e (fun i => base i + z i) := by
  unfold collisionEventEquation at hbase ⊢
  have hzedge : z (collisionEventLeft e) = z (collisionEventRight e) :=
    hz (collisionSubfamilyEvent_connected (q := q) (T := T) heT)
  change (base (collisionEventLeft e) + z (collisionEventLeft e)) -
      (base (collisionEventRight e) + z (collisionEventRight e)) =
        collisionEventLabel y e
  rw [hzedge]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase

/-- Adding a component-constant offset to one solution preserves every labelled
collision equation in the subfamily. -/
theorem collisionSubfamilyEquations_add_componentConstant [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {base z : Fin q → G}
    (hbase : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e base)
    (hz : collisionSubfamilyComponentConstant (q := q) T z) :
    ∀ e ∈ T,
      collisionEventEquation (G := G) (q := q) y e (fun i => base i + z i) := by
  intro e heT
  exact collisionEventEquation_add_componentConstant (G := G) (q := q)
    (y := y) (T := T) (base := base) (z := z) (e := e) (hbase e heT) heT hz

/-- Once one solution exists, all solutions of a labelled subfamily are exactly
that solution plus a component-constant offset. -/
def collisionSubfamilySolutionEquivComponentConstant [AddCommGroup G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {base : Fin q → G}
    (hbase : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e base) :
    { a : Fin q → G // ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e a } ≃
      { z : Fin q → G // collisionSubfamilyComponentConstant (q := q) T z } where
  toFun a :=
    ⟨fun i => a.1 i - base i,
      collisionSubfamilyComponentConstant_of_solution_offsets (G := G) (q := q)
        (y := y) (T := T) (a := a.1) (b := base) a.2 hbase⟩
  invFun z :=
    ⟨fun i => base i + z.1 i,
      collisionSubfamilyEquations_add_componentConstant (G := G) (q := q)
        (y := y) (T := T) (base := base) (z := z.1) hbase z.2⟩
  left_inv a := by
    ext i
    simp only
    abel
  right_inv z := by
    ext i
    simp only
    abel

/-- If a labelled subfamily has one solution, then its solution type has one
free `G`-value per support component. -/
theorem card_collisionSubfamilyEquationSolutions_of_solution [AddCommGroup G]
    [Fintype G] [DecidableEq G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {base : Fin q → G}
    (hbase : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e base) :
    Fintype.card { a : Fin q → G // ∀ e ∈ T,
        collisionEventEquation (G := G) (q := q) y e a } =
      (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T := by
  classical
  rw [Fintype.card_congr
    (collisionSubfamilySolutionEquivComponentConstant (G := G) (q := q)
      (y := y) (T := T) (base := base) hbase)]
  exact card_collisionSubfamilyComponentConstant (G := G) (q := q) T

instance collisionSubfamilyOccursDecidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    DecidablePred (fun a : Fin q → G =>
      collisionSubfamilyOccurs (G := G) (q := q) y T a) :=
  fun _ => Classical.propDecidable _

/-- Number of hidden tuples satisfying all collision equations in a chosen
subfamily.  These are the terms that appear in the eventual
inclusion-exclusion formula. -/
def collisionSubfamilySolutionCount [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter
    (fun a => collisionSubfamilyOccurs (G := G) (q := q) y T a)).card

/-- The hidden tuples triggering one collision event. -/
def collisionEventSet [AddGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G)
    (e : CollisionEvent q) : Finset (Fin q → G) :=
  (Finset.univ : Finset (Fin q → G)).filter
    (fun a => collisionEventOccurs (G := G) (q := q) y e a)

/-- Membership in the intersection of a collision-event subfamily is exactly
satisfaction of every collision equation in that subfamily. -/
theorem mem_inf_collisionEventSet [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) (a : Fin q → G) :
    a ∈ T.inf (collisionEventSet (G := G) (q := q) y) ↔
      ∀ e ∈ T, collisionEventOccurs (G := G) (q := q) y e a := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Finset.inf_empty]
  | insert _ _ _ ih =>
      simp [Finset.inf_insert, ih, collisionEventSet]

/-- Membership in the intersection of collision-event complements is exactly
avoidance of every collision equation in the subfamily. -/
theorem mem_inf_compl_collisionEventSet [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) (a : Fin q → G) :
    a ∈ T.inf (fun e => (collisionEventSet (G := G) (q := q) y e)ᶜ) ↔
      ∀ e ∈ T, ¬ collisionEventOccurs (G := G) (q := q) y e a := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Finset.inf_empty]
  | insert _ T _ ih =>
      have ih' :
          (a ∈ T.inf fun e =>
              ((Finset.univ : Finset (Fin q → G)).filter
                (fun x => ¬ collisionEventOccurs (G := G) (q := q) y e x))) ↔
            ∀ e ∈ T, ¬ collisionEventOccurs (G := G) (q := q) y e a := by
        simpa [collisionEventSet] using ih
      rw [Finset.inf_insert]
      simp [collisionEventSet, ih']

/-- The subfamily solution count is the cardinality of the intersection of the
corresponding event sets. -/
theorem collisionSubfamilySolutionCount_eq_card_inf_eventSets
    [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    collisionSubfamilySolutionCount (G := G) (q := q) y T =
      (T.inf (collisionEventSet (G := G) (q := q) y)).card := by
  unfold collisionSubfamilySolutionCount collisionSubfamilyOccurs
  congr 1
  ext a
  simp [mem_inf_collisionEventSet]

/-- The same subfamily solution count, phrased as a count of assignments
satisfying the labelled equations. -/
theorem collisionSubfamilySolutionCount_eq_card_filter_forall_equations
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    collisionSubfamilySolutionCount (G := G) (q := q) y T =
      ((Finset.univ : Finset (Fin q → G)).filter
        (fun a => ∀ e ∈ T,
          collisionEventEquation (G := G) (q := q) y e a)).card := by
  unfold collisionSubfamilySolutionCount
  congr 1
  ext a
  simp [collisionSubfamilyOccurs_iff_forall_equations]

/-- If a collision-event subfamily has one solution, then its
inclusion-exclusion solution count is `|G|` to the number of support
components. -/
theorem collisionSubfamilySolutionCount_eq_pow_componentCount_of_solution
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)} {base : Fin q → G}
    (hbase : ∀ e ∈ T, collisionEventEquation (G := G) (q := q) y e base) :
    collisionSubfamilySolutionCount (G := G) (q := q) y T =
      (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T := by
  rw [collisionSubfamilySolutionCount_eq_card_filter_forall_equations]
  rw [← Fintype.card_subtype]
  exact card_collisionSubfamilyEquationSolutions_of_solution (G := G) (q := q)
    (y := y) (T := T) (base := base) hbase

/-- An inconsistent labelled subfamily has no satisfying hidden assignments. -/
theorem collisionSubfamilySolutionCount_eq_zero_of_not_consistent
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    {y : Fin q → G} {T : Finset (CollisionEvent q)}
    (hT : ¬ collisionSubfamilyConsistent (G := G) (q := q) y T) :
    collisionSubfamilySolutionCount (G := G) (q := q) y T = 0 := by
  rw [collisionSubfamilySolutionCount_eq_card_filter_forall_equations]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ha hP
  exact hT ⟨a, hP⟩

/-- Every labelled subfamily solution count is either zero or one free
`G`-value per support component, according to semantic consistency. -/
theorem collisionSubfamilySolutionCount_eq_ite_consistent
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    collisionSubfamilySolutionCount (G := G) (q := q) y T =
      if collisionSubfamilyConsistent (G := G) (q := q) y T then
        (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T
      else
        0 := by
  by_cases hT : collisionSubfamilyConsistent (G := G) (q := q) y T
  · rcases hT with ⟨base, hbase⟩
    rw [if_pos ⟨base, hbase⟩]
    exact collisionSubfamilySolutionCount_eq_pow_componentCount_of_solution
      (G := G) (q := q) (y := y) (T := T) (base := base) hbase
  · rw [if_neg hT]
    exact collisionSubfamilySolutionCount_eq_zero_of_not_consistent
      (G := G) (q := q) (y := y) (T := T) hT

/-- The solution count evaluated using the explicit closed-walk consistency
condition. -/
theorem collisionSubfamilySolutionCount_eq_ite_cycleConsistent
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (T : Finset (CollisionEvent q)) :
    collisionSubfamilySolutionCount (G := G) (q := q) y T =
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T
      else
        0 := by
  rw [collisionSubfamilySolutionCount_eq_ite_consistent]
  by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
  · have hsem : collisionSubfamilyConsistent (G := G) (q := q) y T :=
      (collisionSubfamilyConsistent_iff_cycleConsistent (G := G) (q := q) y T).mpr hcyc
    simp [hcyc, hsem]
  · have hsem : ¬ collisionSubfamilyConsistent (G := G) (q := q) y T := by
      intro h
      exact hcyc
        ((collisionSubfamilyConsistent_iff_cycleConsistent (G := G) (q := q) y T).mp h)
    simp [hcyc, hsem]

/-- Inclusion-exclusion over the finite collision-event family.

This is the formal version of the first half of the gain-graph formula: the
compatible count is the alternating sum of solution counts for collision-event
subfamilies.  The remaining gain-graph work is to evaluate each subfamily
solution count by connected components when its labels are cycle-consistent,
and by `0` otherwise. -/
theorem compatibleCountNat_eq_inclusionExclusion_collisionSubfamilies
    [AddGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
        (-1 : ℤ) ^ T.card *
          (collisionSubfamilySolutionCount (G := G) (q := q) y T : ℤ) := by
  rw [compatibleCountNat_eq_card_filter_forall_not_collisionEventOccurs]
  let U : Finset (CollisionEvent q) := Finset.univ
  let S : CollisionEvent q → Finset (Fin q → G) :=
    collisionEventSet (G := G) (q := q) y
  have hleft :
      ((Finset.univ : Finset (Fin q → G)).filter
        (fun a => ∀ e : CollisionEvent q,
          ¬ collisionEventOccurs (G := G) (q := q) y e a)).card =
        (U.inf fun e => (S e)ᶜ).card := by
    congr 1
    ext a
    simpa [U, S] using
      (mem_inf_compl_collisionEventSet (G := G) (q := q) y U a).symm
  rw [hleft]
  have hIE := Finset.inclusion_exclusion_card_inf_compl (s := U) (S := S)
  rw [hIE]
  simp [U, S, collisionSubfamilySolutionCount_eq_card_inf_eventSets]

/-- Inclusion-exclusion with each collision subfamily already evaluated as
either zero or `|G|` to its number of support components.  The consistency
predicate here is semantic satisfiability; the remaining gain-graph work is to
replace it by the cycle-xor condition. -/
theorem compatibleCountNat_eq_inclusionExclusion_consistentSubfamilies
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T
            else
              0) : ℤ) := by
  rw [compatibleCountNat_eq_inclusionExclusion_collisionSubfamilies]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [collisionSubfamilySolutionCount_eq_ite_consistent]
  simp

/-- Inclusion-exclusion with collision subfamilies evaluated by explicit
closed-walk consistency.  This is the formal gain-graph version of Lemma 4. -/
theorem compatibleCountNat_eq_inclusionExclusion_cycleConsistentSubfamilies
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T
            else
              0) : ℤ) := by
  rw [compatibleCountNat_eq_inclusionExclusion_consistentSubfamilies]
  apply Finset.sum_congr rfl
  intro T _hT
  by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
  · have hsem : collisionSubfamilyConsistent (G := G) (q := q) y T :=
      (collisionSubfamilyConsistent_iff_cycleConsistent (G := G) (q := q) y T).mpr hcyc
    simp [hcyc, hsem]
  · have hsem : ¬ collisionSubfamilyConsistent (G := G) (q := q) y T := by
      intro h
      exact hcyc
        ((collisionSubfamilyConsistent_iff_cycleConsistent (G := G) (q := q) y T).mp h)
    simp [hcyc, hsem]

/-- Gain-graph inclusion-exclusion grouped by graphic rank. -/
theorem compatibleCountNat_eq_rankSum_cycleConsistentSubfamilies
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ∑ r : Fin (q + 1),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T
              else
                0) : ℤ) := by
  rw [compatibleCountNat_eq_inclusionExclusion_cycleConsistentSubfamilies]
  exact (Finset.sum_fiberwise
    ((Finset.univ : Finset (CollisionEvent q)).powerset)
    (collisionSubfamilyGraphicRankFin (q := q))
    (fun T =>
      (-1 : ℤ) ^ T.card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) T
          else
            0) : ℤ))).symm

/-- Gain-graph inclusion-exclusion grouped by graphic rank, with the exponent
written as `q - r`.  This is the rank-stratified form used for tail estimates. -/
theorem compatibleCountNat_eq_rankSum_cycleConsistentSubfamilies_explicit
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ∑ r : Fin (q + 1),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^ (q - r.val)
              else
                0) : ℤ) := by
  rw [compatibleCountNat_eq_rankSum_cycleConsistentSubfamilies]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  have hrankNat : collisionSubfamilyGraphicRank (q := q) T = r.val := by
    exact congrArg Fin.val hT.2
  have hcomp : collisionSubfamilyComponentCount (q := q) T = q - r.val := by
    rw [collisionSubfamilyComponentCount_eq_query_sub_graphicRank (q := q) T, hrankNat]
  by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
  · simp [hcyc, hcomp]
  · simp [hcyc]

/-- The rank-`r` layer of the gain-graph inclusion-exclusion formula for the
compatible hidden-state count.  This is the reusable object for separating the
main rank-zero/rank-one contribution from the higher-rank tail. -/
def collisionSubfamilyRankLayerInt [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (r : Fin (q + 1)) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRankFin (q := q) T = r,
    (-1 : ℤ) ^ T.card *
      ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
          (Fintype.card G) ^ (q - r.val)
        else
          0) : ℤ)

/-- Rank-layer form of the gain-graph inclusion-exclusion formula. -/
theorem compatibleCountNat_eq_sum_rankLayers
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ∑ r : Fin (q + 1), collisionSubfamilyRankLayerInt (G := G) (q := q) y r := by
  simpa [collisionSubfamilyRankLayerInt] using
    compatibleCountNat_eq_rankSum_cycleConsistentSubfamilies_explicit
      (G := G) (q := q) y

/-- A labelled walk in the empty collision-event subfamily has accumulated
label zero. -/
theorem collisionSubfamilyLabelReach_empty_eq_zero [AddGroup G]
    {y : Fin q → G} {i j : Fin q} {label : G}
    (h : collisionSubfamilyLabelReach (G := G) (q := q) y ∅ i j label) :
    label = 0 := by
  induction h with
  | refl => rfl
  | tail _hprev hstep _ih =>
      rcases hstep with ⟨_e, he, _hends⟩
      simp at he

/-- The empty collision-event subfamily is cycle-consistent. -/
theorem collisionSubfamilyCycleConsistent_empty [AddGroup G] (y : Fin q → G) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y ∅ := by
  intro _i _label h
  exact collisionSubfamilyLabelReach_empty_eq_zero (G := G) (q := q) h

/-- A single collision equation is always satisfiable. -/
theorem collisionSubfamilyConsistent_singleton [AddCommGroup G]
    (y : Fin q → G) (e : CollisionEvent q) :
    collisionSubfamilyConsistent (G := G) (q := q) y {e} := by
  refine ⟨fun i => if i = collisionEventLeft e then collisionEventLabel y e else 0, ?_⟩
  intro e' he'
  have heq : e' = e := by simpa using he'
  subst e'
  unfold collisionEventEquation
  have hne : collisionEventRight e ≠ collisionEventLeft e :=
    (ne_of_lt (collisionEventLeft_lt_right (q := q) e)).symm
  simp [hne]

/-- A singleton collision-event subfamily is cycle-consistent. -/
theorem collisionSubfamilyCycleConsistent_singleton [AddCommGroup G]
    (y : Fin q → G) (e : CollisionEvent q) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y {e} :=
  (collisionSubfamilyConsistent_iff_cycleConsistent (G := G) (q := q) y {e}).mp
    (collisionSubfamilyConsistent_singleton (G := G) (q := q) y e)

/-- Two same-endpoint collision events are semantically consistent exactly when
their labels agree. -/
theorem collisionSubfamilyConsistent_pair_sameEndpoints_iff_label_eq [AddCommGroup G]
    (y : Fin q → G) {e₁ e₂ : CollisionEvent q}
    (hl : collisionEventLeft e₂ = collisionEventLeft e₁)
    (hr : collisionEventRight e₂ = collisionEventRight e₁) :
    collisionSubfamilyConsistent (G := G) (q := q) y
        ({e₁, e₂} : Finset (CollisionEvent q)) ↔
      collisionEventLabel y e₁ = collisionEventLabel y e₂ := by
  constructor
  · intro hT
    rcases hT with ⟨a, ha⟩
    have h₁ := ha e₁ (by simp)
    have h₂ := ha e₂ (by simp)
    unfold collisionEventEquation at h₁ h₂
    have h₂' :
        a (collisionEventLeft e₁) - a (collisionEventRight e₁) =
          collisionEventLabel y e₂ := by
      simpa [hl, hr] using h₂
    exact h₁.symm.trans h₂'
  · intro hlabel
    rcases collisionSubfamilyConsistent_singleton (G := G) (q := q) y e₁ with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he
    · subst e
      exact ha e₁ (by simp)
    · subst e
      have h₁ := ha e₁ (by simp)
      unfold collisionEventEquation at h₁ ⊢
      simpa [hl, hr, hlabel] using h₁

/-- Two same-endpoint collision events are cycle-consistent exactly when their
labels agree. -/
theorem collisionSubfamilyCycleConsistent_pair_sameEndpoints_iff_label_eq [AddCommGroup G]
    (y : Fin q → G) {e₁ e₂ : CollisionEvent q}
    (hl : collisionEventLeft e₂ = collisionEventLeft e₁)
    (hr : collisionEventRight e₂ = collisionEventRight e₁) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
        ({e₁, e₂} : Finset (CollisionEvent q)) ↔
      collisionEventLabel y e₁ = collisionEventLabel y e₂ := by
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  exact collisionSubfamilyConsistent_pair_sameEndpoints_iff_label_eq (G := G) (q := q) y hl hr

/-- For one query pair, the hidden and shifted collision labels agree exactly
when the two visible outputs on that pair are equal. -/
theorem collisionEventLabel_hidden_eq_shifted_iff [AddCommGroup G]
    (y : Fin q → G) (p : PairIndex q) :
    collisionEventLabel y (p, CollisionKind.hidden) =
        collisionEventLabel y (p, CollisionKind.shifted) ↔
      y p.1.2 = y p.1.1 := by
  constructor
  · intro h
    have hzero : y p.1.2 - y p.1.1 = 0 := by
      simpa [collisionEventLabel, collisionEventLeft, collisionEventRight] using h.symm
    exact sub_eq_zero.mp hzero
  · intro h
    have hzero : y p.1.2 - y p.1.1 = 0 := sub_eq_zero.mpr h
    simpa [collisionEventLabel, collisionEventLeft, collisionEventRight] using hzero.symm

/-- The two parallel hidden/shifted constraints for one query pair are
cycle-consistent exactly at visible equality on that pair. -/
theorem collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff [AddCommGroup G]
    (y : Fin q → G) (p : PairIndex q) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
        ({(p, CollisionKind.hidden), (p, CollisionKind.shifted)} :
          Finset (CollisionEvent q)) ↔
      y p.1.2 = y p.1.1 := by
  rw [collisionSubfamilyCycleConsistent_pair_sameEndpoints_iff_label_eq
    (G := G) (q := q) y (by rfl) (by rfl)]
  exact collisionEventLabel_hidden_eq_shifted_iff (G := G) (q := q) y p

/-- Any subfamily of the pair-local event set has the same endpoints as the
hidden event on that pair. -/
theorem collisionSubfamilySameEndpoints_of_subset_collisionPairEvents
    (p : PairIndex q) {T : Finset (CollisionEvent q)}
    (hT : T ⊆ collisionPairEvents (q := q) p) :
    collisionSubfamilySameEndpoints (q := q) (p, CollisionKind.hidden) T := by
  intro e he
  have hepair := hT he
  simp only [collisionPairEvents, Finset.mem_insert, Finset.mem_singleton] at hepair
  rcases hepair with heq | heq
  · subst e
    simp [collisionEventLeft, collisionEventRight]
  · subst e
    simp [collisionEventLeft, collisionEventRight]

/-- Membership in a pair-local event set fixes the underlying query pair of the
event. -/
theorem collisionEvent_pairIndex_eq_of_mem_collisionPairEvents
    {p : PairIndex q} {e : CollisionEvent q}
    (he : e ∈ collisionPairEvents (q := q) p) :
    e.1 = p := by
  simp only [collisionPairEvents, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with he | he <;> subst e <;> rfl

/-- A nonempty collision-event subfamily is contained in at most one pair-local
event set. -/
theorem collisionPairEvents_subset_unique_of_nonempty
    {T : Finset (CollisionEvent q)} (hne : T.Nonempty)
    {p₁ p₂ : PairIndex q}
    (h₁ : T ⊆ collisionPairEvents (q := q) p₁)
    (h₂ : T ⊆ collisionPairEvents (q := q) p₂) :
    p₁ = p₂ := by
  rcases hne with ⟨e, he⟩
  have hp₁ : e.1 = p₁ :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (h₁ he)
  have hp₂ : e.1 = p₂ :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (h₂ he)
  exact hp₁.symm.trans hp₂

/-- Every nonempty subfamily of one pair-local event set has graphic rank one. -/
theorem collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
    (p : PairIndex q) {T : Finset (CollisionEvent q)}
    (hne : T.Nonempty) (hT : T ⊆ collisionPairEvents (q := q) p) :
    collisionSubfamilyGraphicRank (q := q) T = 1 :=
  collisionSubfamilyGraphicRank_eq_one_of_sameEndpoints (q := q)
    (p, CollisionKind.hidden) hne
    (collisionSubfamilySameEndpoints_of_subset_collisionPairEvents (q := q) p hT)

/-- Graphic-rank-one support families are exactly the nonempty subfamilies of
one pair-local event set. -/
theorem collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
    (T : Finset (CollisionEvent q)) :
    collisionSubfamilyGraphicRank (q := q) T = 1 ↔
      T.Nonempty ∧ ∃ p : PairIndex q, T ⊆ collisionPairEvents (q := q) p := by
  constructor
  · intro hrank
    have hne : T.Nonempty := by
      by_contra hempty
      have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      subst T
      simp [collisionSubfamilyGraphicRank_empty] at hrank
    rcases hne with ⟨e, he⟩
    exact ⟨⟨e, he⟩,
      ⟨e.1, collisionSubfamily_subset_collisionPairEvents_of_graphicRank_eq_one
        (q := q) hrank he⟩⟩
  · rintro ⟨hne, p, hT⟩
    exact collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
      (q := q) p hne hT

/-- The unique query pair supporting a graphic-rank-one collision-event
subfamily. -/
def collisionSubfamilyRankOnePair (T : Finset (CollisionEvent q))
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1) : PairIndex q :=
  Classical.choose
    ((collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
      (q := q) T).mp hrank).2

/-- A graphic-rank-one collision-event subfamily is nonempty. -/
theorem collisionSubfamilyRankOne_nonempty
    {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1) :
    T.Nonempty :=
  ((collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
    (q := q) T).mp hrank).1

/-- The rank-one pair classifier supports the original subfamily. -/
theorem collisionSubfamily_subset_rankOnePairEvents
    {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1) :
    T ⊆ collisionPairEvents (q := q) (collisionSubfamilyRankOnePair (q := q) T hrank) :=
  Classical.choose_spec
    ((collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
      (q := q) T).mp hrank).2

/-- The rank-one pair classifier is the unique pair-local support. -/
theorem collisionSubfamilyRankOnePair_eq_of_subset
    {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1)
    {p : PairIndex q} (hT : T ⊆ collisionPairEvents (q := q) p) :
    collisionSubfamilyRankOnePair (q := q) T hrank = p :=
  collisionPairEvents_subset_unique_of_nonempty (q := q)
    (collisionSubfamilyRankOne_nonempty (q := q) hrank)
    (collisionSubfamily_subset_rankOnePairEvents (q := q) hrank) hT

/-- A total rank-one support classifier, returning `none` away from the
rank-one layer.  This is the version suited to `Finset.sum_fiberwise`. -/
def collisionSubfamilyRankOnePairOption
    (T : Finset (CollisionEvent q)) : Option (PairIndex q) :=
  if hrank : collisionSubfamilyGraphicRank (q := q) T = 1 then
    some (collisionSubfamilyRankOnePair (q := q) T hrank)
  else
    none

/-- The optional rank-one classifier has fiber `p` exactly on the nonempty
subfamilies of the pair-local event set for `p`. -/
theorem collisionSubfamilyRankOnePairOption_eq_some_iff
    {T : Finset (CollisionEvent q)} {p : PairIndex q} :
    collisionSubfamilyRankOnePairOption (q := q) T = some p ↔
      T.Nonempty ∧ T ⊆ collisionPairEvents (q := q) p := by
  unfold collisionSubfamilyRankOnePairOption
  by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 1
  · simp only [hrank, dite_true, Option.some.injEq]
    constructor
    · intro hp
      constructor
      · exact collisionSubfamilyRankOne_nonempty (q := q) hrank
      · rw [← hp]
        exact collisionSubfamily_subset_rankOnePairEvents (q := q) hrank
    · intro hT
      exact collisionSubfamilyRankOnePair_eq_of_subset (q := q) hrank hT.2
  · simp only [hrank, dite_false, reduceCtorEq]
    constructor
    · intro h
      exact False.elim h
    · intro hT
      exact False.elim
        (hrank (collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
          (q := q) p hT.1 hT.2))

/-- The `some p` fiber of the optional rank-one classifier is exactly the
nonempty powerset of the pair-local event family for `p`. -/
theorem collisionSubfamilyRankOnePairOption_fiber_eq_pairPowerset
    (p : PairIndex q) :
    ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => collisionSubfamilyRankOnePairOption (q := q) T = some p)) =
      ((collisionPairEvents (q := q) p).powerset.filter fun T => T.Nonempty) := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro h
    have hfiber :=
      (collisionSubfamilyRankOnePairOption_eq_some_iff
        (q := q) (T := T) (p := p)).mp h.2
    exact ⟨hfiber.2, hfiber.1⟩
  · intro h
    exact ⟨by simp, (collisionSubfamilyRankOnePairOption_eq_some_iff
      (q := q) (T := T) (p := p)).mpr ⟨h.2, h.1⟩⟩

/-- The graphic-rank-one subfamilies are exactly the union of the nonempty
pair-local powersets. -/
theorem collisionSubfamilyRankOneSubfamilies_eq_biUnion_pairPowersets :
    ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => collisionSubfamilyGraphicRank (q := q) T = 1)) =
      (Finset.univ : Finset (PairIndex q)).biUnion
        (fun p => (collisionPairEvents (q := q) p).powerset.filter fun T => T.Nonempty) := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  constructor
  · intro h
    rcases (collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
      (q := q) T).mp h.2 with ⟨hne, p, hsub⟩
    exact ⟨p, hsub, hne⟩
  · rintro ⟨p, hsub, hne⟩
    exact ⟨by simp,
      collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
        (q := q) p hne hsub⟩

/-- The finite-rank-one fiber is the same pair-local union, stated for the
finite rank classifier used by the rank-stratified formula. -/
theorem collisionSubfamilyRankOneFinSubfamilies_eq_biUnion_pairPowersets
    (hq : 0 < q) :
    ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => collisionSubfamilyGraphicRankFin (q := q) T =
        collisionSubfamilyGraphicRankOneFin hq)) =
      (Finset.univ : Finset (PairIndex q)).biUnion
        (fun p => (collisionPairEvents (q := q) p).powerset.filter fun T => T.Nonempty) := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  constructor
  · intro h
    have hrank : collisionSubfamilyGraphicRank (q := q) T = 1 := by
      exact congrArg Fin.val h.2
    rcases (collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
      (q := q) T).mp hrank with ⟨hne, p, hsub⟩
    exact ⟨p, hsub, hne⟩
  · rintro ⟨p, hsub, hne⟩
    have hrank :
        collisionSubfamilyGraphicRank (q := q) T = 1 :=
      collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
        (q := q) p hne hsub
    exact ⟨by simp, Fin.ext hrank⟩

/-- The nonempty pair-local powersets for distinct query pairs are disjoint. -/
theorem collisionPairEvents_powerset_nonempty_pairwiseDisjoint :
    (Set.univ : Set (PairIndex q)).PairwiseDisjoint
      (fun p => (collisionPairEvents (q := q) p).powerset.filter fun T => T.Nonempty) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro p _hp p' _hp' hnonempty
  rcases hnonempty with ⟨T, hT⟩
  have hTp : T ∈ (collisionPairEvents (q := q) p).powerset.filter fun T => T.Nonempty :=
    (Finset.mem_inter.mp hT).1
  have hTp' : T ∈ (collisionPairEvents (q := q) p').powerset.filter fun T => T.Nonempty :=
    (Finset.mem_inter.mp hT).2
  simp only [Finset.mem_filter, Finset.mem_powerset] at hTp hTp'
  exact collisionPairEvents_subset_unique_of_nonempty (q := q) hTp.2 hTp.1 hTp'.1

/-- The rank-zero collision-event subfamilies consist only of the empty
subfamily. -/
theorem collisionSubfamilyRankZeroSubfamilies_eq_singleton :
    ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => collisionSubfamilyGraphicRank (q := q) T = 0)) = {∅} := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · intro h
    exact collisionSubfamily_eq_empty_of_graphicRank_eq_zero (q := q) h.2
  · intro h
    subst h
    constructor
    · simp
    · exact collisionSubfamilyGraphicRank_empty (q := q)

/-- Each query-pair local event family has exactly three nonempty
subfamilies: the two singleton constraints and the full hidden/shifted pair. -/
theorem collisionPairEvents_powerset_nonempty_card (p : PairIndex q) :
    ((collisionPairEvents (q := q) p).powerset.filter fun T => T.Nonempty).card = 3 := by
  rw [collisionPairEvents]
  rw [finset_pair_powerset_filter_nonempty]
  · simp [finset_singleton_ne_pair_left, finset_singleton_ne_pair_right,
      collisionKind_hidden_ne_shifted]
  · intro h
    have hk : CollisionKind.hidden = CollisionKind.shifted := by
      exact congrArg Prod.snd h
    exact collisionKind_hidden_ne_shifted hk

/-- There are three graphic-rank-one collision-event subfamilies for each
query pair. -/
theorem collisionSubfamilyRankOneSubfamilies_card :
    (((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => collisionSubfamilyGraphicRank (q := q) T = 1)).card) =
      3 * Fintype.card (PairIndex q) := by
  rw [collisionSubfamilyRankOneSubfamilies_eq_biUnion_pairPowersets]
  rw [Finset.card_biUnion (by
    simpa using collisionPairEvents_powerset_nonempty_pairwiseDisjoint (q := q))]
  simp [collisionPairEvents_powerset_nonempty_card, Finset.sum_const, mul_comm]

/-- The low-rank collision-event subfamilies are exactly the empty subfamily
and the rank-one pair-local subfamilies. -/
theorem collisionSubfamilyLowRankSubfamilies_card :
    (((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => ¬ 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card) =
      1 + 3 * Fintype.card (PairIndex q) := by
  let U : Finset (Finset (CollisionEvent q)) :=
    (Finset.univ : Finset (CollisionEvent q)).powerset
  let zeroSet := U.filter (fun T => collisionSubfamilyGraphicRank (q := q) T = 0)
  let oneSet := U.filter (fun T => collisionSubfamilyGraphicRank (q := q) T = 1)
  have hlow : U.filter (fun T => ¬ 2 ≤ collisionSubfamilyGraphicRank (q := q) T) =
      zeroSet ∪ oneSet := by
    ext T
    simp only [zeroSet, oneSet, U, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      have hcases : collisionSubfamilyGraphicRank (q := q) T = 0 ∨
          collisionSubfamilyGraphicRank (q := q) T = 1 := by omega
      rcases hcases with h0 | h1
      · exact Or.inl ⟨h.1, h0⟩
      · exact Or.inr ⟨h.1, h1⟩
    · intro h
      rcases h with h0 | h1
      · exact ⟨h0.1, by omega⟩
      · exact ⟨h1.1, by omega⟩
  have hdisj : Disjoint zeroSet oneSet := by
    rw [Finset.disjoint_left]
    intro T hzero hone
    simp only [zeroSet, Finset.mem_filter] at hzero
    simp only [oneSet, Finset.mem_filter] at hone
    omega
  have hzeroCard : zeroSet.card = 1 := by
    have hz : zeroSet =
        ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => collisionSubfamilyGraphicRank (q := q) T = 0)) := rfl
    rw [hz, collisionSubfamilyRankZeroSubfamilies_eq_singleton]
    simp
  have honeCard : oneSet.card = 3 * Fintype.card (PairIndex q) := by
    have ho : oneSet =
        ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => collisionSubfamilyGraphicRank (q := q) T = 1)) := rfl
    rw [ho]
    exact collisionSubfamilyRankOneSubfamilies_card (q := q)
  change (U.filter (fun T => ¬ 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card =
    1 + 3 * Fintype.card (PairIndex q)
  rw [hlow]
  rw [Finset.card_union_of_disjoint hdisj]
  rw [hzeroCard, honeCard]

/-- The rank-tail subfamilies plus the completely counted low-rank
subfamilies exhaust the powerset of collision events. -/
theorem collisionSubfamilyRankTailSubfamilies_card_add_lowRank_card :
    (((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card) +
      (1 + 3 * Fintype.card (PairIndex q)) =
    ((Finset.univ : Finset (CollisionEvent q)).powerset.card) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (CollisionEvent q)).powerset)
    (p := fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)
  rw [collisionSubfamilyLowRankSubfamilies_card] at hsplit
  exact hsplit

/-- Exact cardinality of the rank-tail subfamilies, after removing the already
counted rank-zero and rank-one layers from the collision-event powerset. -/
theorem collisionSubfamilyRankTailSubfamilies_card_eq :
    (((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card) =
      2 ^ (q * (q - 1)) - (1 + 3 * Fintype.card (PairIndex q)) := by
  have hsum := collisionSubfamilyRankTailSubfamilies_card_add_lowRank_card (q := q)
  rw [collisionEvent_univ_powerset_card, collisionEvent_card_eq_query_pair_twice] at hsum
  omega

/-- The full pair-local event set is cycle-consistent exactly at visible
equality on that pair. -/
theorem collisionPairEvents_cycleConsistent_iff [AddCommGroup G]
    (y : Fin q → G) (p : PairIndex q) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionPairEvents (q := q) p) ↔
      y p.1.2 = y p.1.1 := by
  simpa [collisionPairEvents] using
    collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff (G := G) (q := q) y p

/-- The pair-local alternating coefficient for nonempty subfamilies: two
singleton constraints always contribute `-1` each, and the full pair contributes
`+1` exactly when the visible outputs on the pair are equal. -/
theorem collisionPairEvents_localAlternatingCoefficient [AddCommGroup G] [DecidableEq G]
    (y : Fin q → G) (p : PairIndex q) :
    (-1 : ℤ) ^ ({(p, CollisionKind.hidden)} : Finset (CollisionEvent q)).card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y
          ({(p, CollisionKind.hidden)} : Finset (CollisionEvent q)) then 1 else 0) : ℤ) +
      (-1 : ℤ) ^ ({(p, CollisionKind.shifted)} : Finset (CollisionEvent q)).card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y
          ({(p, CollisionKind.shifted)} : Finset (CollisionEvent q)) then 1 else 0) : ℤ) +
      (-1 : ℤ) ^ (collisionPairEvents (q := q) p).card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y
          (collisionPairEvents (q := q) p) then 1 else 0) : ℤ) =
      -2 + (if y p.1.2 = y p.1.1 then 1 else 0) := by
  by_cases h : y p.1.2 = y p.1.1
  · have hpair : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        ({(p, CollisionKind.hidden), (p, CollisionKind.shifted)} :
          Finset (CollisionEvent q)) := by
      exact (collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff
        (G := G) (q := q) y p).mpr h
    simp [collisionPairEvents, collisionSubfamilyCycleConsistent_singleton, hpair, h]
  · have hpair : ¬ collisionSubfamilyCycleConsistent (G := G) (q := q) y
        ({(p, CollisionKind.hidden), (p, CollisionKind.shifted)} :
          Finset (CollisionEvent q)) := by
      intro hcyc
      exact h ((collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff
        (G := G) (q := q) y p).mp hcyc)
    simp [collisionPairEvents, collisionSubfamilyCycleConsistent_singleton, hpair, h]

/-- The pair-local alternating coefficient as an actual sum over all nonempty
subfamilies of the pair-local event set. -/
theorem collisionPairEvents_localPowersetAlternatingCoefficient
    [AddCommGroup G] [DecidableEq G] (y : Fin q → G) (p : PairIndex q) :
    ((collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)).sum (fun T =>
      (-1 : ℤ) ^ T.card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then 1 else 0) : ℤ)) =
      -2 + (if y p.1.2 = y p.1.1 then 1 else 0) := by
  rw [show (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty) =
      ({{(p, CollisionKind.hidden)}, {(p, CollisionKind.shifted)},
        collisionPairEvents (q := q) p} : Finset (Finset (CollisionEvent q))) by
    simpa [collisionPairEvents] using
      finset_pair_powerset_filter_nonempty
        (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp)]
  by_cases h : y p.1.2 = y p.1.1
  · have hpair : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        ({(p, CollisionKind.hidden), (p, CollisionKind.shifted)} :
          Finset (CollisionEvent q)) := by
      exact (collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff
        (G := G) (q := q) y p).mpr h
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        simp [collisionPairEvents, collisionSubfamilyCycleConsistent_singleton, hpair, h]
      · simpa using finset_singleton_ne_pair_right
          (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp)
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsingle | hpair
      · have hkind : CollisionKind.hidden = CollisionKind.shifted := by
          exact congrArg Prod.snd (Finset.singleton_inj.mp hsingle)
        cases hkind
      · exact finset_singleton_ne_pair_left
          (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp) hpair
  · have hpair : ¬ collisionSubfamilyCycleConsistent (G := G) (q := q) y
        ({(p, CollisionKind.hidden), (p, CollisionKind.shifted)} :
          Finset (CollisionEvent q)) := by
      intro hcyc
      exact h ((collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff
        (G := G) (q := q) y p).mp hcyc)
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        simp [collisionPairEvents, collisionSubfamilyCycleConsistent_singleton, hpair, h]
      · simpa using finset_singleton_ne_pair_right
          (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp)
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsingle | hpair
      · have hkind : CollisionKind.hidden = CollisionKind.shifted := by
          exact congrArg Prod.snd (Finset.singleton_inj.mp hsingle)
        cases hkind
      · exact finset_singleton_ne_pair_left
          (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp) hpair

/-- Ite-shaped version of the pair-local alternating coefficient, matching the
rank-stratified formula after simplifying multiplication by an indicator. -/
theorem collisionPairEvents_localPowersetAlternatingCoefficient_ite
    [AddCommGroup G] [DecidableEq G] (y : Fin q → G) (p : PairIndex q) :
    ((collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)).sum (fun T =>
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0) =
      -2 + (if y p.1.2 = y p.1.1 then 1 else 0) := by
  simpa [mul_ite] using
    collisionPairEvents_localPowersetAlternatingCoefficient (G := G) (q := q) y p

/-- The full graphic-rank-one alternating coefficient is the sum of the
pair-local coefficients over query pairs. -/
theorem collisionSubfamily_rankOneLayerAlternatingCoefficient
    [AddCommGroup G] [DecidableEq G] (y : Fin q → G) (hq : 0 < q) :
    (∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
      collisionSubfamilyGraphicRankFin (q := q) T = collisionSubfamilyGraphicRankOneFin hq,
      (-1 : ℤ) ^ T.card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then 1 else 0) : ℤ)) =
      ∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ) := by
  rw [collisionSubfamilyRankOneFinSubfamilies_eq_biUnion_pairPowersets (q := q) hq]
  rw [Finset.sum_biUnion (by
    simpa using collisionPairEvents_powerset_nonempty_pairwiseDisjoint (q := q))]
  apply Finset.sum_congr rfl
  intro p _hp
  exact collisionPairEvents_localPowersetAlternatingCoefficient (G := G) (q := q) y p

/-- The rank-one layer as it appears in the rank-stratified compatible-count
formula: the pair-local coefficient multiplied by `|G|^(q-1)`. -/
theorem collisionSubfamily_rankOneLayer_eq_card_pow_mul_pairCoefficient
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) (hq : 0 < q) :
    (∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
      collisionSubfamilyGraphicRankFin (q := q) T = collisionSubfamilyGraphicRankOneFin hq,
      (-1 : ℤ) ^ T.card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - (collisionSubfamilyGraphicRankOneFin hq).val)
          else
            0) : ℤ)) =
      ((Fintype.card G) ^ (q - 1) : ℤ) *
        ∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ) := by
  rw [← collisionSubfamily_rankOneLayerAlternatingCoefficient (G := G) (q := q) y hq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
  · simp [hcyc, collisionSubfamilyGraphicRankOneFin, mul_comm]
  · simp [hcyc]

/-- Named rank-layer version of the rank-one contribution. -/
theorem collisionSubfamily_rankLayer_one_eq_card_pow_mul_pairCoefficient
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) (hq : 0 < q) :
    collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankOneFin hq) =
      ((Fintype.card G) ^ (q - 1) : ℤ) *
        ∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ) := by
  simpa [collisionSubfamilyRankLayerInt] using
    collisionSubfamily_rankOneLayer_eq_card_pow_mul_pairCoefficient
      (G := G) (q := q) y hq

/-- The rank-zero plus rank-one compatible-count approximation.  This is the
part of the gain-graph expansion that should produce the spatial reconstruction
bound; the remaining difference is the higher-rank tail. -/
def compatibleCountLowRankInt
    [Fintype G] [DecidableEq G]
    (y : Fin q → G) : ℤ :=
  ((Fintype.card G) ^ q : ℤ) +
    ((Fintype.card G) ^ (q - 1) : ℤ) *
      ∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ)

/-- The residual after removing the rank-zero and rank-one layers from the
gain-graph expansion.  This is the exact object that later tail estimates must
bound; no asymptotic estimate is built into the definition. -/
def collisionSubfamilyRankResidualBeyondOneInt
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) : ℤ :=
  (compatibleCountNat (G := G) (q := q) y : ℤ) -
    collisionSubfamilyRankLayerInt (G := G) (q := q) y ⟨0, Nat.zero_lt_succ q⟩ -
    collisionSubfamilyRankLayerInt (G := G) (q := q) y
      (collisionSubfamilyGraphicRankOneFin hq)

/-- The rank-zero layer of the rank-stratified gain-graph formula contributes
exactly the unconstrained hidden-state count `|G|^q`. -/
theorem collisionSubfamily_rankZeroLayer_eq_card_fun
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    (∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
      collisionSubfamilyGraphicRankFin (q := q) T = ⟨0, Nat.zero_lt_succ q⟩,
      (-1 : ℤ) ^ T.card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - (0 : Fin (q + 1)).val)
          else
            0) : ℤ)) = ((Fintype.card G) ^ q : ℤ) := by
  have hfilter : ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => collisionSubfamilyGraphicRankFin (q := q) T = ⟨0, Nat.zero_lt_succ q⟩)) =
      {∅} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · intro h
      exact collisionSubfamily_eq_empty_of_graphicRank_eq_zero (q := q)
        (congrArg Fin.val h.2)
    · intro h
      subst h
      constructor
      · simp
      · apply Fin.ext
        simp [collisionSubfamilyGraphicRankFin, collisionSubfamilyGraphicRank_empty]
  rw [hfilter]
  simp [collisionSubfamilyCycleConsistent_empty]

/-- Named rank-layer version of the rank-zero contribution. -/
theorem collisionSubfamily_rankLayer_zero_eq_card_fun
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    collisionSubfamilyRankLayerInt (G := G) (q := q) y ⟨0, Nat.zero_lt_succ q⟩ =
      ((Fintype.card G) ^ q : ℤ) := by
  simpa [collisionSubfamilyRankLayerInt] using
    collisionSubfamily_rankZeroLayer_eq_card_fun (G := G) (q := q) y

/-- Exact decomposition of the compatible hidden-state count into the proved
rank-zero layer, the proved rank-one layer, and the remaining rank residual. -/
theorem compatibleCountNat_eq_rankZero_add_rankOne_add_residual
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) (hq : 0 < q) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ((Fintype.card G) ^ q : ℤ) +
      ((Fintype.card G) ^ (q - 1) : ℤ) *
        ∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ) +
      collisionSubfamilyRankResidualBeyondOneInt (G := G) (q := q) y hq := by
  unfold collisionSubfamilyRankResidualBeyondOneInt
  rw [collisionSubfamily_rankLayer_zero_eq_card_fun (G := G) (q := q) y]
  rw [collisionSubfamily_rankLayer_one_eq_card_pow_mul_pairCoefficient
    (G := G) (q := q) y hq]
  ring

/-- The explicit higher-rank tail: all rank layers except rank zero and rank
one.  This is the filtered-sum object to use for later tail bounds. -/
def collisionSubfamilyRankTailBeyondOneInt
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) : ℤ :=
  ∑ r ∈ (Finset.univ.erase (⟨0, Nat.zero_lt_succ q⟩ : Fin (q + 1))).erase
      (collisionSubfamilyGraphicRankOneFin hq),
    collisionSubfamilyRankLayerInt (G := G) (q := q) y r

/-- The algebraic residual after removing ranks zero and one is exactly the
filtered sum of the remaining rank layers. -/
theorem collisionSubfamilyRankResidualBeyondOneInt_eq_tail
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    collisionSubfamilyRankResidualBeyondOneInt (G := G) (q := q) y hq =
      collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq := by
  unfold collisionSubfamilyRankResidualBeyondOneInt collisionSubfamilyRankTailBeyondOneInt
  rw [compatibleCountNat_eq_sum_rankLayers (G := G) (q := q) y]
  let z : Fin (q + 1) := ⟨0, Nat.zero_lt_succ q⟩
  let o : Fin (q + 1) := collisionSubfamilyGraphicRankOneFin hq
  have hz : z ∈ (Finset.univ : Finset (Fin (q + 1))) := Finset.mem_univ z
  have ho : o ∈ (Finset.univ.erase z) := by
    simp [z, o, collisionSubfamilyGraphicRankOneFin]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin (q + 1)))
    (fun r => collisionSubfamilyRankLayerInt (G := G) (q := q) y r) hz]
  rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin (q + 1))).erase z)
    (fun r => collisionSubfamilyRankLayerInt (G := G) (q := q) y r) ho]
  simp [z, o, add_comm, add_left_comm]
  ring

/-- The same higher-rank tail, written as the sum over ranks whose numeric
rank is at least two. -/
theorem collisionSubfamilyRankTailBeyondOneInt_eq_sum_rank_ge_two
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq =
      ∑ r ∈ (Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val)),
        collisionSubfamilyRankLayerInt (G := G) (q := q) y r := by
  unfold collisionSubfamilyRankTailBeyondOneInt
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hne1 : r.val ≠ 1 := by
        intro hv
        apply h.1
        apply Fin.ext
        simpa [collisionSubfamilyGraphicRankOneFin] using hv
      have hne0 : r.val ≠ 0 := by
        intro hv
        apply h.2.1
        apply Fin.ext
        simpa using hv
      omega
    · intro h
      constructor
      · intro hr
        have hv : r.val = 1 := congrArg Fin.val hr
        simp at hv
        omega
      · constructor
        · intro hr
          have hv : r.val = 0 := congrArg Fin.val hr
          omega
        · trivial
  · intro r _
    rfl

/-- The higher-rank tail as a single inclusion-exclusion sum over collision
subfamilies whose graphic rank is at least two.  This is the form suited to
direct combinatorial estimates. -/
theorem collisionSubfamilyRankTailBeyondOneInt_eq_subfamily_sum_rank_ge_two
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq =
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ) := by
  rw [collisionSubfamilyRankTailBeyondOneInt_eq_sum_rank_ge_two
    (G := G) (q := q) y hq]
  unfold collisionSubfamilyRankLayerInt
  calc
    (∑ r ∈ Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^ (q - r.val)
              else
                0) : ℤ)) =
      ∑ r ∈ Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro T hT
        simp only [Finset.mem_filter] at hT
        rw [hT.2]
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        collisionSubfamilyGraphicRankFin (q := q) T ∈
          (Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val)),
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ) := by
        exact Finset.sum_fiberwise_eq_sum_filter
          ((Finset.univ : Finset (CollisionEvent q)).powerset)
          (Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val))
          (collisionSubfamilyGraphicRankFin (q := q))
          (fun T => (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ))
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ) := by
        apply Finset.sum_congr
        · ext T
          simp [collisionSubfamilyGraphicRankFin]
        · intro T _hT
          simp [collisionSubfamilyGraphicRankFin]

/-- A collision-event subfamily of graphic rank at least two contains at least
two events. -/
theorem collisionSubfamily_card_ge_two_of_graphicRank_ge_two
    {T : Finset (CollisionEvent q)}
    (hrank : 2 ≤ collisionSubfamilyGraphicRank (q := q) T) :
    2 ≤ T.card := by
  by_contra h
  have hcases : T.card = 0 ∨ T.card = 1 := by omega
  rcases hcases with hcard | hcard
  · have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    subst T
    simp [collisionSubfamilyGraphicRank_empty] at hrank
  · rcases Finset.card_eq_one.mp hcard with ⟨e, hT⟩
    subst T
    simp [collisionSubfamilyGraphicRank_singleton] at hrank

/-- Exact compatible-count decomposition using the explicit higher-rank tail. -/
theorem compatibleCountNat_eq_rankZero_add_rankOne_add_tail
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) (hq : 0 < q) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      ((Fintype.card G) ^ q : ℤ) +
      ((Fintype.card G) ^ (q - 1) : ℤ) *
        ∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ) +
      collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq := by
  rw [compatibleCountNat_eq_rankZero_add_rankOne_add_residual
    (G := G) (q := q) y hq]
  rw [collisionSubfamilyRankResidualBeyondOneInt_eq_tail (G := G) (q := q) y hq]

/-- Compatible counts split into the named low-rank approximation plus the
higher-rank tail. -/
theorem compatibleCountNat_eq_lowRank_add_tail
    [AddCommGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) (hq : 0 < q) :
    (compatibleCountNat (G := G) (q := q) y : ℤ) =
      compatibleCountLowRankInt (G := G) (q := q) y +
        collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq := by
  rw [compatibleCountNat_eq_rankZero_add_rankOne_add_tail (G := G) (q := q) y hq]
  rfl

/-- Triangle-inequality bound for the higher-rank tail, retaining the
cycle-consistency filter. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_le_sum_consistent_terms
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
  rw [collisionSubfamilyRankTailBeyondOneInt_eq_subfamily_sum_rank_ge_two
    (G := G) (q := q) y hq]
  calc
    |∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        |(-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro T _hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp [hcyc, abs_mul]
        · simp [hcyc]

/-- Coarser triangle-inequality bound for the higher-rank tail, dropping the
cycle-consistency filter. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_le_sum_rank_terms
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T) : ℤ) := by
  calc
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
        exact abs_collisionSubfamilyRankTailBeyondOneInt_le_sum_consistent_terms
          (G := G) (q := q) y hq
    _ ≤ ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T) : ℤ) := by
        apply Finset.sum_le_sum
        intro T _hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp [hcyc]
        · simp [hcyc]

/-- Coarse bound for the higher-rank tail by the number of rank-tail
subfamilies times `|G|^(q-2)`. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_le_tailCard_mul_card_pow
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card : Nat) *
        (Fintype.card G) ^ (q - 2) : ℤ) := by
  calc
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T) : ℤ) := by
        exact abs_collisionSubfamilyRankTailBeyondOneInt_le_sum_rank_terms
          (G := G) (q := q) y hq
    _ ≤ ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        2 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((Fintype.card G) ^ (q - 2) : ℤ) := by
        apply Finset.sum_le_sum
        intro T hT
        simp only [Finset.mem_filter] at hT
        have hle_exp :
            q - collisionSubfamilyGraphicRank (q := q) T ≤ q - 2 := by
          omega
        exact_mod_cast Nat.pow_le_pow_right
          (Nat.succ_le_of_lt Fintype.card_pos) hle_exp
    _ = ((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card : Nat) *
        (Fintype.card G) ^ (q - 2) : ℤ) := by
        simp

/-- Closed-form version of `abs_collisionSubfamilyRankTailBeyondOneInt_le_tailCard_mul_card_pow`,
subtracting the already-counted rank-zero and rank-one subfamilies from the
full collision-event powerset. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_le_explicitTailCard_mul_card_pow
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      (((2 ^ (q * (q - 1)) - (1 + 3 * Fintype.card (PairIndex q))) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
  have h :=
    abs_collisionSubfamilyRankTailBeyondOneInt_le_tailCard_mul_card_pow
      (G := G) (q := q) y hq
  rw [collisionSubfamilyRankTailSubfamilies_card_eq] at h
  simpa using h

/-- Pointwise compatible-count error after replacing the true compatible count
by the rank-zero plus rank-one approximation. -/
theorem abs_compatibleCountNat_sub_lowRank_le_explicitTailCard_mul_card_pow
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |(compatibleCountNat (G := G) (q := q) y : ℤ) -
        compatibleCountLowRankInt (G := G) (q := q) y| ≤
      (((2 ^ (q * (q - 1)) - (1 + 3 * Fintype.card (PairIndex q))) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
  rw [compatibleCountNat_eq_lowRank_add_tail (G := G) (q := q) y hq]
  simpa using
    abs_collisionSubfamilyRankTailBeyondOneInt_le_explicitTailCard_mul_card_pow
      (G := G) (q := q) y hq

/-- Multiplicative form of the exact low-rank/tail split, useful for tail
estimates with a common `|G|^(q-2)` factor. -/
theorem collisionSubfamilyRankTailSubfamilies_card_mul_add_lowRank_mul
    (m : Nat) :
    (((Finset.univ : Finset (CollisionEvent q)).powerset.filter
      (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card) * m +
      (1 + 3 * Fintype.card (PairIndex q)) * m =
    ((Finset.univ : Finset (CollisionEvent q)).powerset.card) * m := by
  rw [← Nat.add_mul]
  rw [collisionSubfamilyRankTailSubfamilies_card_add_lowRank_card]

/-- Additive version of the tail-card improvement: the already-counted low-rank
part can be added to the absolute tail estimate without exceeding the crude
full-powerset bound.  This is the subtraction-free form needed for later `Nat`
arithmetic. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_add_lowRank_mul_card_pow_le_powersetCard_mul_card_pow
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| +
      (((1 + 3 * Fintype.card (PairIndex q)) * (Fintype.card G) ^ (q - 2) : Nat) : ℤ) ≤
      ((((Finset.univ : Finset (CollisionEvent q)).powerset.card : Nat) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
  have htail := abs_collisionSubfamilyRankTailBeyondOneInt_le_tailCard_mul_card_pow
    (G := G) (q := q) y hq
  have hnat := collisionSubfamilyRankTailSubfamilies_card_mul_add_lowRank_mul
    (q := q) ((Fintype.card G) ^ (q - 2))
  calc
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| +
      (((1 + 3 * Fintype.card (PairIndex q)) * (Fintype.card G) ^ (q - 2) : Nat) : ℤ) ≤
        (((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card : Nat) *
          (Fintype.card G) ^ (q - 2) : Nat) : ℤ) +
      (((1 + 3 * Fintype.card (PairIndex q)) * (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
        exact add_le_add htail (le_refl _)
    _ = ((((Finset.univ : Finset (CollisionEvent q)).powerset.card : Nat) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
        exact_mod_cast hnat

/-- Coarser bound for the higher-rank tail by all collision-event subfamilies.
This is not intended to be sharp; it is a reusable fallback until sharper
rank-tail graph counts are available. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_le_powersetCard_mul_card_pow
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ((((Finset.univ : Finset (CollisionEvent q)).powerset.card : Nat) *
        (Fintype.card G) ^ (q - 2) : ℤ)) := by
  calc
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => 2 ≤ collisionSubfamilyGraphicRank (q := q) T)).card : Nat) *
        (Fintype.card G) ^ (q - 2) : ℤ) := by
        exact abs_collisionSubfamilyRankTailBeyondOneInt_le_tailCard_mul_card_pow
          (G := G) (q := q) y hq
    _ ≤ ((((Finset.univ : Finset (CollisionEvent q)).powerset.card : Nat) *
        (Fintype.card G) ^ (q - 2) : ℤ)) := by
        exact_mod_cast Nat.mul_le_mul_right ((Fintype.card G) ^ (q - 2))
          (Finset.card_le_card (Finset.filter_subset _ _))

/-- Coarse closed-form version of the higher-rank tail bound, using the fact
that there are `q * (q - 1)` hidden/shifted collision events. -/
theorem abs_collisionSubfamilyRankTailBeyondOneInt_le_queryEvent_pow_mul_card_pow
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) (hq : 0 < q) :
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ((((2 : Nat) ^ (q * (q - 1))) * (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
  calc
    |collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq| ≤
      ((((Finset.univ : Finset (CollisionEvent q)).powerset.card : Nat) *
        (Fintype.card G) ^ (q - 2) : ℤ)) := by
        exact abs_collisionSubfamilyRankTailBeyondOneInt_le_powersetCard_mul_card_pow
          (G := G) (q := q) y hq
    _ = ((((2 : Nat) ^ Fintype.card (CollisionEvent q)) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
        rw [collisionEvent_univ_powerset_card]
        norm_num
    _ = ((((2 : Nat) ^ (q * (q - 1))) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
        rw [collisionEvent_card_eq_query_pair_twice]

@[simp]
theorem collisionSubfamilyOccurs_empty [AddGroup G] (y a : Fin q → G) :
    collisionSubfamilyOccurs (G := G) (q := q) y ∅ a := by
  intro e he
  simp at he

@[simp]
theorem collisionSubfamilySolutionCount_empty
    [AddGroup G] [Fintype G] [DecidableEq G] (y : Fin q → G) :
    collisionSubfamilySolutionCount (G := G) (q := q) y ∅ =
      Fintype.card (Fin q → G) := by
  unfold collisionSubfamilySolutionCount
  simp

end SoP
end Applications
end RandomSystems
