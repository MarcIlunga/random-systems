/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.XoPMayer
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-!
# XoP Rank/Codimension Scaffold

This file starts XOP-DAG-12.  It defines the colored constraint atoms that are
allowed only after the pair-Mayer expansion boundary in `XoPMayer.lean`.

The rank/codimension theorem itself is still open, but its inputs are now typed:
hidden atoms impose `a_i = a_j`; shifted atoms impose
`a_i + y_i = a_j + y_j`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Rank

open ANOVA Mayer

variable {G K : Type*} {q : Nat}

/-- The two colored atoms obtained from a pair-level bad event. -/
inductive AtomColor where
  | hidden
  | shifted
deriving DecidableEq

instance atomColorFintype : Fintype AtomColor where
  elems := {AtomColor.hidden, AtomColor.shifted}
  complete := by
    intro c
    cases c <;> simp

/-- A colored constraint atom attached to a pair edge. -/
structure Atom (S : Finset (Fin q)) where
  edge : PairEdge S
  color : AtomColor

instance atomDecidableEq (S : Finset (Fin q)) : DecidableEq (Atom S) :=
  Classical.decEq _

/-- Monotone embedding of pair edges along support inclusion. -/
def pairEdge_mono {U S : Finset (Fin q)} (hUS : U ⊆ S) (e : PairEdge U) :
    PairEdge S :=
  ⟨e.1, hUS e.2.1, hUS e.2.2.1, e.2.2.2⟩

/-- Monotone embedding of colored atoms along support inclusion.  This is the
block-to-support bridge required by support-partition atomized evaluations. -/
def atom_mono {U S : Finset (Fin q)} (hUS : U ⊆ S) (A : Atom U) : Atom S :=
  ⟨pairEdge_mono hUS A.edge, A.color⟩

theorem atom_mono_injective {U S : Finset (Fin q)} (hUS : U ⊆ S) :
    Function.Injective (atom_mono (q := q) hUS) := by
  intro A B h
  cases A with
  | mk eA cA =>
    cases B with
    | mk eB cB =>
      cases eA with
      | mk valA propA =>
        cases eB with
        | mk valB propB =>
          cases cA <;> cases cB <;> simp [atom_mono, pairEdge_mono] at h ⊢
          · cases h
            rfl
          · cases h
            rfl

@[simp]
theorem atom_mono_color {U S : Finset (Fin q)} (hUS : U ⊆ S) (A : Atom U) :
    (atom_mono hUS A).color = A.color := by
  rfl

@[simp]
theorem atom_mono_edge_value {U S : Finset (Fin q)} (hUS : U ⊆ S) (A : Atom U) :
    (atom_mono hUS A).edge.1 = A.edge.1 := by
  rfl

instance atomFintype (S : Finset (Fin q)) : Fintype (Atom S) := by
  classical
  exact Fintype.ofEquiv (PairEdge S × AtomColor)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun a => (a.edge, a.color)
      left_inv := by intro p; rfl
      right_inv := by intro a; cases a; rfl }

/-- Semantics of one colored atom on a visible tuple `y` and hidden tuple `a`. -/
def atomHolds [AddGroup G] (y a : Fin q → G) {S : Finset (Fin q)} (A : Atom S) : Prop :=
  match A.color with
  | AtomColor.hidden => pairBadHidden a A.edge.1
  | AtomColor.shifted => pairBadShifted y a A.edge.1

instance atomHolds_decidable [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) {S : Finset (Fin q)} (A : Atom S) :
    Decidable (atomHolds y a A) := by
  cases A with
  | mk e c =>
      cases c <;> unfold atomHolds <;> infer_instance

/-- The hidden atom attached to a pair edge. -/
def hiddenAtom {S : Finset (Fin q)} (e : PairEdge S) : Atom S :=
  ⟨e, AtomColor.hidden⟩

/-- The shifted atom attached to a pair edge. -/
def shiftedAtom {S : Finset (Fin q)} (e : PairEdge S) : Atom S :=
  ⟨e, AtomColor.shifted⟩

@[simp]
theorem atomHolds_hidden [AddGroup G] (y a : Fin q → G) {S : Finset (Fin q)}
    (e : PairEdge S) :
    atomHolds y a (hiddenAtom e) ↔ pairBadHidden a e.1 := by
  rfl

@[simp]
theorem atomHolds_shifted [AddGroup G] (y a : Fin q → G) {S : Finset (Fin q)}
    (e : PairEdge S) :
    atomHolds y a (shiftedAtom e) ↔ pairBadShifted y a e.1 := by
  rfl

@[simp]
theorem atomHolds_atom_mono [AddGroup G] {U S : Finset (Fin q)} (hUS : U ⊆ S)
    (y a : Fin q → G) (A : Atom U) :
    atomHolds y a (atom_mono hUS A) ↔ atomHolds y a A := by
  cases A with
  | mk e c =>
      cases c <;> rfl

/-- A pair bad event is exactly the existence of a hidden or shifted atom on the
same pair edge. -/
theorem pairBad_iff_exists_atomHolds [AddGroup G] {S : Finset (Fin q)}
    (y a : Fin q → G) (e : PairEdge S) :
    pairBad y a e.1 ↔ ∃ c : AtomColor, atomHolds y a ⟨e, c⟩ := by
  constructor
  · intro hbad
    rcases hbad with hhidden | hshifted
    · exact ⟨AtomColor.hidden, hhidden⟩
    · exact ⟨AtomColor.shifted, hshifted⟩
  · intro h
    rcases h with ⟨c, hc⟩
    cases c with
    | hidden => exact Or.inl hc
    | shifted => exact Or.inr hc

/-- Vertices touched by an atom family are inherited from the underlying pair
edges. -/
def atomVertices {S : Finset (Fin q)} (A : Finset (Atom S)) : Finset (Fin q) :=
  A.biUnion (fun atom => {atom.edge.1.1, atom.edge.1.2})

@[simp]
theorem atomVertices_empty {S : Finset (Fin q)} :
    atomVertices (S := S) (∅ : Finset (Atom S)) = ∅ := by
  simp [atomVertices]

theorem atom_edge_left_mem_atomVertices {S : Finset (Fin q)} {A : Finset (Atom S)}
    {atom : Atom S} (hatom : atom ∈ A) :
    atom.edge.1.1 ∈ atomVertices A := by
  rw [atomVertices]
  exact Finset.mem_biUnion.mpr ⟨atom, hatom, by simp⟩

theorem atom_edge_right_mem_atomVertices {S : Finset (Fin q)} {A : Finset (Atom S)}
    {atom : Atom S} (hatom : atom ∈ A) :
    atom.edge.1.2 ∈ atomVertices A := by
  rw [atomVertices]
  exact Finset.mem_biUnion.mpr ⟨atom, hatom, by simp⟩

theorem atomVertices_subset {S : Finset (Fin q)} (A : Finset (Atom S)) :
    atomVertices A ⊆ S := by
  intro i hi
  simp [atomVertices] at hi
  rcases hi with ⟨atom, _hatom, hi | hi⟩
  · subst hi
    exact atom.edge.2.1
  · subst hi
    exact atom.edge.2.2.1

/-- Linear form `a_i - a_j` associated with an oriented pair edge. -/
def edgeDifferenceLinearForm (K : Type*) [Field K] (e : (Fin q) × (Fin q)) :
    (Fin q → K) →ₗ[K] K :=
  (LinearMap.proj e.1 : (Fin q → K) →ₗ[K] K) -
    (LinearMap.proj e.2 : (Fin q → K) →ₗ[K] K)

@[simp]
theorem edgeDifferenceLinearForm_apply (K : Type*) [Field K]
    (e : (Fin q) × (Fin q)) (a : Fin q → K) :
    edgeDifferenceLinearForm (q := q) K e a = a e.1 - a e.2 := by
  rfl

/-- The right-hand side of an atom equation after moving hidden variables to
the left.  Hidden atoms have RHS `0`; shifted atoms have RHS `y_j - y_i`. -/
def atomRhs [Field K] (y : Fin q → K) {S : Finset (Fin q)} (A : Atom S) : K :=
  match A.color with
  | AtomColor.hidden => 0
  | AtomColor.shifted => y A.edge.1.2 - y A.edge.1.1

/-- Linear form of a colored atom.  Both hidden and shifted atoms use the same
hidden-variable form; only the RHS changes. -/
def atomLinearForm (K : Type*) [Field K] {S : Finset (Fin q)} (_A : Atom S) :
    (Fin q → K) →ₗ[K] K :=
  edgeDifferenceLinearForm (q := q) K _A.edge.1

@[simp]
theorem atomLinearForm_atom_mono (K : Type*) [Field K]
    {U S : Finset (Fin q)} (hUS : U ⊆ S) (A : Atom U) :
    atomLinearForm (q := q) K (atom_mono hUS A) = atomLinearForm (q := q) K A := by
  rfl

@[simp]
theorem atomRhs_atom_mono [Field K]
    {U S : Finset (Fin q)} (hUS : U ⊆ S) (y : Fin q → K) (A : Atom U) :
    atomRhs y (atom_mono hUS A) = atomRhs y A := by
  cases A with
  | mk _ c =>
      cases c <;> rfl

/-- Atom satisfaction is equivalent to the corresponding affine linear
equation over a field. -/
theorem atomHolds_iff_linearForm_eq [Field K] (y a : Fin q → K)
    {S : Finset (Fin q)} (A : Atom S) :
    atomHolds y a A ↔ atomLinearForm (q := q) K A a = atomRhs y A := by
  cases A with
  | mk e c =>
      cases c with
      | hidden =>
          simp [atomHolds, atomLinearForm, atomRhs, edgeDifferenceLinearForm,
            pairBadHidden, sub_eq_zero]
      | shifted =>
          constructor
          · intro h
            have h' : a e.1.1 - a e.1.2 = y e.1.2 - y e.1.1 := by
              have hraw : a e.1.1 + y e.1.1 = a e.1.2 + y e.1.2 := by
                simpa [atomHolds, pairBadShifted] using h
              rw [sub_eq_sub_iff_add_eq_add]
              simpa [add_comm, add_left_comm, add_assoc] using hraw
            simpa [atomLinearForm, atomRhs, edgeDifferenceLinearForm] using h'
          · intro h
            have hraw : a e.1.1 + y e.1.1 = a e.1.2 + y e.1.2 := by
              have h' : a e.1.1 - a e.1.2 = y e.1.2 - y e.1.1 := by
                simpa [atomLinearForm, atomRhs, edgeDifferenceLinearForm] using h
              have hadd := sub_eq_sub_iff_add_eq_add.mp h'
              simpa [add_comm, add_left_comm, add_assoc] using hadd
            simpa [atomHolds, pairBadShifted] using hraw

/-- Hidden constraint map for a finite family of atom rows. -/
def hiddenConstraintMap (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) :
    (Fin q → K) →ₗ[K] (ρ → K) :=
  LinearMap.pi fun r => atomLinearForm (q := q) K (row r)

/-- Visible right-hand-side map for a finite family of atom rows. -/
def visibleRhsMap (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) :
    (Fin q → K) →ₗ[K] (ρ → K) :=
  LinearMap.pi fun r =>
    match (row r).color with
    | AtomColor.hidden => 0
    | AtomColor.shifted => edgeDifferenceLinearForm (q := q) K ((row r).edge.1.2, (row r).edge.1.1)

@[simp]
theorem hiddenConstraintMap_apply (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) (a : Fin q → K) (r : ρ) :
    hiddenConstraintMap (q := q) K row a r = atomLinearForm (q := q) K (row r) a := by
  rfl

@[simp]
theorem visibleRhsMap_apply (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) (y : Fin q → K) (r : ρ) :
    visibleRhsMap (q := q) K row y r = atomRhs y (row r) := by
  cases hrow : row r with
  | mk e c =>
      cases c <;> simp [visibleRhsMap, atomRhs, edgeDifferenceLinearForm, hrow]

/-- A hidden tuple satisfies every row iff the hidden constraint vector equals
the visible RHS vector. -/
theorem all_atomHolds_iff_hiddenConstraintMap_eq_visibleRhsMap [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S)
    (y a : Fin q → K) :
    (∀ r : ρ, atomHolds y a (row r)) ↔
      hiddenConstraintMap (q := q) K row a = visibleRhsMap (q := q) K row y := by
  constructor
  · intro h
    funext r
    simpa [hiddenConstraintMap_apply, visibleRhsMap_apply] using
      (atomHolds_iff_linearForm_eq (K := K) y a (row r)).mp (h r)
  · intro h r
    apply (atomHolds_iff_linearForm_eq (K := K) y a (row r)).mpr
    simpa [hiddenConstraintMap_apply, visibleRhsMap_apply] using congrFun h r

/-- Quotient obstruction of visible RHS vectors modulo the hidden row space. -/
def visibleObstructionMap (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) :
    (Fin q → K) →ₗ[K] ((ρ → K) ⧸ (hiddenConstraintMap (q := q) K row).range) :=
  (Submodule.mkQ (hiddenConstraintMap (q := q) K row).range).comp
    (visibleRhsMap (q := q) K row)

/-- Fixed-visible hidden feasibility is equivalent to vanishing of the visible
obstruction in the quotient by the hidden row space. -/
theorem exists_hidden_solution_iff_visibleObstruction_eq_zero [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S)
    (y : Fin q → K) :
    (∃ a : Fin q → K, hiddenConstraintMap (q := q) K row a =
      visibleRhsMap (q := q) K row y) ↔
        visibleObstructionMap (q := q) K row y = 0 := by
  unfold visibleObstructionMap
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩

/-- Hidden rank of an atom row family: dimension of the hidden row space. -/
def hiddenRank (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) : Nat :=
  Module.finrank K (hiddenConstraintMap (q := q) K row).range

/-- Visible obstruction rank: dimension of the quotient-visible defect image. -/
def visibleObstructionRank (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) : Nat :=
  Module.finrank K (visibleObstructionMap (q := q) K row).range

/-- Joint hidden/visible constraint map.  Its kernel is the linearized space of
pairs `(a, y)` satisfying all atom rows. -/
def jointConstraintMap (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) :
    ((Fin q → K) × (Fin q → K)) →ₗ[K] (ρ → K) :=
  (hiddenConstraintMap (q := q) K row).comp (LinearMap.fst K (Fin q → K) (Fin q → K)) -
    (visibleRhsMap (q := q) K row).comp (LinearMap.snd K (Fin q → K) (Fin q → K))

/-- Joint rank of the combined hidden/visible linearized system. -/
def jointRank (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) : Nat :=
  Module.finrank K (jointConstraintMap (q := q) K row).range

@[simp]
theorem jointConstraintMap_apply (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) (ay : (Fin q → K) × (Fin q → K)) :
    jointConstraintMap (q := q) K row ay =
      hiddenConstraintMap (q := q) K row ay.1 - visibleRhsMap (q := q) K row ay.2 := by
  rfl

/-- The range of a product-domain difference map is the sum of the two
component ranges. -/
theorem range_sub_prod_eq_sup {A B W : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup W] [Module K W] (H : A →ₗ[K] W) (V : B →ₗ[K] W) :
    LinearMap.range (H.comp (LinearMap.fst K A B) - V.comp (LinearMap.snd K A B)) =
      H.range ⊔ V.range := by
  apply le_antisymm
  · rintro z ⟨ab, rfl⟩
    exact Submodule.sub_mem _
      ((le_sup_left : H.range ≤ H.range ⊔ V.range) ⟨ab.1, rfl⟩)
      ((le_sup_right : V.range ≤ H.range ⊔ V.range) ⟨ab.2, rfl⟩)
  · apply sup_le
    · rintro z ⟨a, rfl⟩
      exact ⟨(a, 0), by simp⟩
    · rintro z ⟨b, rfl⟩
      exact ⟨(0, -b), by simp⟩

/-- The range of a quotient-composed map is the quotient image of the original
range. -/
theorem range_mkQ_comp_eq_map {A W : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (V : A →ₗ[K] W) :
    LinearMap.range (S.mkQ.comp V) = V.range.map S.mkQ := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨V a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

/-- Dimension of an image in a quotient: the quotient-visible image contributes
exactly the dimension missing from the base subspace to the joined subspace. -/
theorem finrank_map_mkQ_add_finrank_eq_finrank_sup {W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (S T : Submodule K W) :
    Module.finrank K (T.map S.mkQ) + Module.finrank K S = Module.finrank K ↥(S ⊔ T) := by
  have h1 := Submodule.finrank_quotient_add_finrank (R := K) (M := W ⧸ S) (T.map S.mkQ)
  have h2 := Submodule.finrank_quotient_add_finrank (R := K) (M := W) S
  have h3 := Submodule.finrank_quotient_add_finrank (R := K) (M := W) (S ⊔ T)
  have hquot :
      Module.finrank K ((W ⧸ S) ⧸ T.map S.mkQ) =
        Module.finrank K (W ⧸ (S ⊔ T)) := by
    exact LinearEquiv.finrank_eq
      (Submodule.quotientQuotientEquivQuotientSup (S := S) (T := T))
  omega

/-- The exact rank identity needed for the atomized rank/codimension route.  The
visible obstruction rank is the part of the joint row rank not already forced by
hidden constraints. -/
theorem visibleObstructionRank_add_hiddenRank_eq_jointRank [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S) :
    visibleObstructionRank (q := q) K row + hiddenRank (q := q) K row =
      jointRank (q := q) K row := by
  let H := hiddenConstraintMap (q := q) K row
  let V := visibleRhsMap (q := q) K row
  have hvisible :
      visibleObstructionRank (q := q) K row = Module.finrank K (V.range.map H.range.mkQ) := by
    dsimp [visibleObstructionRank, visibleObstructionMap, H, V]
    exact congrArg (fun U : Submodule K ((ρ → K) ⧸ H.range) => Module.finrank K U)
      (range_mkQ_comp_eq_map H.range V)
  have hjoint : jointRank (q := q) K row = Module.finrank K ↥(H.range ⊔ V.range) := by
    dsimp [jointRank, jointConstraintMap, H, V]
    exact congrArg (fun U : Submodule K (ρ → K) => Module.finrank K U)
      (range_sub_prod_eq_sup H V)
  rw [hvisible, hjoint]
  exact finrank_map_mkQ_add_finrank_eq_finrank_sup (K := K) H.range V.range

/-- A nonempty affine fiber of a linear map is a translate of its kernel. -/
noncomputable def affineFiberEquivKer {V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] W) (b : W) (a0 : V) (ha0 : L a0 = b) :
    {a : V // L a = b} ≃ LinearMap.ker L where
  toFun a := ⟨a.1 - a0, by
    show L (a.1 - a0) = 0
    rw [LinearMap.map_sub, a.2, ha0, sub_self]
  ⟩
  invFun k := ⟨k.1 + a0, by
    rw [LinearMap.map_add, k.2, ha0, zero_add]
  ⟩
  left_inv a := by
    ext
    simp
  right_inv k := by
    ext
    simp

/-- Feasible hidden row systems have solution fibers equivalent to the kernel of
the hidden constraint map. -/
noncomputable def hiddenSolutionFiberEquivKer [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S)
    (y : Fin q → K)
    (hfeas : ∃ a : Fin q → K,
      hiddenConstraintMap (q := q) K row a = visibleRhsMap (q := q) K row y) :
    {a : Fin q → K // hiddenConstraintMap (q := q) K row a =
      visibleRhsMap (q := q) K row y} ≃
        LinearMap.ker (hiddenConstraintMap (q := q) K row) :=
  affineFiberEquivKer (K := K) (hiddenConstraintMap (q := q) K row)
    (visibleRhsMap (q := q) K row y) (Classical.choose hfeas)
    (Classical.choose_spec hfeas)

/-- Cardinality of a feasible hidden solution fiber over a finite field.  This
is the fixed-bond counting bridge used before the graph-specific rank lower
bounds are applied. -/
theorem hiddenSolutionFiber_card_eq_pow_of_feasible [Field K] [Fintype K] [DecidableEq K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S)
    (y : Fin q → K)
    (hfeas : ∃ a : Fin q → K,
      hiddenConstraintMap (q := q) K row a = visibleRhsMap (q := q) K row y) :
    Fintype.card {a : Fin q → K // hiddenConstraintMap (q := q) K row a =
      visibleRhsMap (q := q) K row y} =
        Fintype.card K ^ (q - hiddenRank (q := q) K row) := by
  let L := hiddenConstraintMap (q := q) K row
  letI : Fintype (LinearMap.ker L) := Fintype.ofFinite (LinearMap.ker L)
  have hcard_fiber_ker :
      Fintype.card {a : Fin q → K // hiddenConstraintMap (q := q) K row a =
        visibleRhsMap (q := q) K row y} = Fintype.card (LinearMap.ker L) := by
    exact Fintype.card_congr (hiddenSolutionFiberEquivKer (q := q) (K := K) row y hfeas)
  have hker_card :
      Fintype.card (LinearMap.ker L) =
        Fintype.card K ^ Module.finrank K (LinearMap.ker L) := by
    exact Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker L)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdom : Module.finrank K (Fin q → K) = q := by
    exact Module.finrank_fin_fun (R := K) (n := q)
  have hker_rank : Module.finrank K (LinearMap.ker L) =
      q - hiddenRank (q := q) K row := by
    dsimp [hiddenRank, L] at hsum ⊢
    omega
  rw [hcard_fiber_ker, hker_card, hker_rank]

/-- Infeasible hidden row systems have no hidden solutions. -/
theorem hiddenSolutionFiber_card_eq_zero_of_infeasible [Field K] [Fintype K] [DecidableEq K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S)
    (y : Fin q → K)
    (hinfeas : ¬ ∃ a : Fin q → K,
      hiddenConstraintMap (q := q) K row a = visibleRhsMap (q := q) K row y) :
    Fintype.card {a : Fin q → K // hiddenConstraintMap (q := q) K row a =
      visibleRhsMap (q := q) K row y} = 0 := by
  have hEmpty :
      IsEmpty {a : Fin q → K // hiddenConstraintMap (q := q) K row a =
      visibleRhsMap (q := q) K row y} :=
    ⟨fun a => hinfeas ⟨a.1, a.2⟩⟩
  exact Fintype.card_eq_zero

/-- A selected atom family holds when every selected hidden/shifted atom holds. -/
def AtomFamilyHolds [AddGroup G] (y a : Fin q → G) {S : Finset (Fin q)}
    (A : Finset (Atom S)) : Prop :=
  ∀ atom ∈ A, atomHolds y a atom

/-- Lift a finite atom family from a block support to a larger ambient
support. -/
def atomFamily_mono {U S : Finset (Fin q)} (hUS : U ⊆ S)
    (A : Finset (Atom U)) : Finset (Atom S) :=
  A.image (atom_mono hUS)

theorem atomFamilyHolds_atomFamily_mono_iff [AddGroup G] [DecidableEq G]
    {U S : Finset (Fin q)} (hUS : U ⊆ S)
    (y a : Fin q → G) (A : Finset (Atom U)) :
    AtomFamilyHolds y a (atomFamily_mono hUS A) ↔ AtomFamilyHolds y a A := by
  unfold AtomFamilyHolds atomFamily_mono
  constructor
  · intro h atom hatom
    have himage : atom_mono hUS atom ∈ A.image (atom_mono hUS) :=
      Finset.mem_image.mpr ⟨atom, hatom, rfl⟩
    exact (atomHolds_atom_mono hUS y a atom).mp (h (atom_mono hUS atom) himage)
  · intro h atom hatom
    rcases Finset.mem_image.mp hatom with ⟨atom0, h0, rfl⟩
    exact (atomHolds_atom_mono hUS y a atom0).mpr (h atom0 h0)

/-- Ambient atom family obtained by lifting and unioning one atom family from
each block of a support partition. -/
def supportPartitionAtomFamily {S : Finset (Fin q)}
    (P : Finpartition S)
    (blockAtoms : (B : P.parts) → Finset (Atom B.1)) : Finset (Atom S) :=
  P.parts.attach.biUnion fun B => atomFamily_mono (P.subset B.2) (blockAtoms B)

theorem atomFamilyHolds_supportPartitionAtomFamily_iff [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (P : Finpartition S)
    (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y a : Fin q → G) :
    AtomFamilyHolds y a (supportPartitionAtomFamily P blockAtoms) ↔
      ∀ B : P.parts, AtomFamilyHolds y a (blockAtoms B) := by
  unfold supportPartitionAtomFamily AtomFamilyHolds atomFamily_mono
  constructor
  · intro h B atom hatom
    have hmem : atom_mono (P.subset B.2) atom ∈
        P.parts.attach.biUnion
          (fun B => Finset.image (atom_mono (P.subset B.2)) (blockAtoms B)) := by
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨B, Finset.mem_attach _ B, Finset.mem_image.mpr ⟨atom, hatom, rfl⟩⟩
    exact (atomHolds_atom_mono (P.subset B.2) y a atom).mp
      (h (atom_mono (P.subset B.2) atom) hmem)
  · intro h atom hatom
    rcases Finset.mem_biUnion.mp hatom with ⟨B, _hB, hBatom⟩
    rcases Finset.mem_image.mp hBatom with ⟨atom0, h0, rfl⟩
    exact (atomHolds_atom_mono (P.subset B.2) y a atom0).mpr (h B atom0 h0)

/-- Atom-family satisfaction only depends on hidden coordinates touched by the
family.  This is the local-to-global bridge used when assembling one hidden
assignment from independent support-partition block assignments. -/
theorem atomFamilyHolds_congr_on_atomVertices [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} {A : Finset (Atom S)}
    {y a a' : Fin q → G}
    (h : ∀ i ∈ atomVertices A, a i = a' i) :
    AtomFamilyHolds y a A ↔ AtomFamilyHolds y a' A := by
  constructor
  · intro hholds atom hatom
    have hleft : a atom.edge.1.1 = a' atom.edge.1.1 :=
      h atom.edge.1.1 (atom_edge_left_mem_atomVertices (q := q) hatom)
    have hright : a atom.edge.1.2 = a' atom.edge.1.2 :=
      h atom.edge.1.2 (atom_edge_right_mem_atomVertices (q := q) hatom)
    have hraw := hholds atom hatom
    cases atom with
    | mk e color =>
        cases color <;> simpa [atomHolds, pairBadHidden, pairBadShifted, hleft, hright] using hraw
  · intro hholds atom hatom
    have hleft : a atom.edge.1.1 = a' atom.edge.1.1 :=
      h atom.edge.1.1 (atom_edge_left_mem_atomVertices (q := q) hatom)
    have hright : a atom.edge.1.2 = a' atom.edge.1.2 :=
      h atom.edge.1.2 (atom_edge_right_mem_atomVertices (q := q) hatom)
    have hraw := hholds atom hatom
    cases atom with
    | mk e color =>
        cases color <;> simpa [atomHolds, pairBadHidden, pairBadShifted, hleft, hright] using hraw

/-- A support-level form of `atomFamilyHolds_congr_on_atomVertices`. -/
theorem atomFamilyHolds_congr_on_support [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} {A : Finset (Atom S)}
    {y a a' : Fin q → G}
    (h : ∀ i ∈ S, a i = a' i) :
    AtomFamilyHolds y a A ↔ AtomFamilyHolds y a' A := by
  exact atomFamilyHolds_congr_on_atomVertices (q := q) (G := G)
    (fun i hi => h i (atomVertices_subset (q := q) A hi))

theorem atomVertices_atomFamily_mono {U S : Finset (Fin q)} (hUS : U ⊆ S)
    (A : Finset (Atom U)) :
    atomVertices (atomFamily_mono hUS A) = atomVertices A := by
  unfold atomVertices atomFamily_mono
  ext i
  simp

theorem atomVertices_supportPartitionAtomFamily {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    atomVertices (supportPartitionAtomFamily P blockAtoms) =
      P.parts.attach.biUnion (fun B => atomVertices (blockAtoms B)) := by
  unfold supportPartitionAtomFamily atomVertices atomFamily_mono
  ext i
  simp

theorem atomVertices_supportPartitionAtomFamily_eq_of_blocks {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hblocks : ∀ B : P.parts, atomVertices (blockAtoms B) = B.1) :
    atomVertices (supportPartitionAtomFamily P blockAtoms) = S := by
  rw [atomVertices_supportPartitionAtomFamily]
  ext i
  constructor
  · intro hi
    simp only [Finset.mem_biUnion, Finset.mem_attach] at hi
    rcases hi with ⟨B, _hB, hiB⟩
    have hiB' : i ∈ B.1 := by simpa [hblocks B] using hiB
    exact P.subset B.2 hiB'
  · intro hiS
    rcases P.exists_mem hiS with ⟨B, hB, hiB⟩
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨⟨B, hB⟩, by simp, ?_⟩
    simpa [hblocks ⟨B, hB⟩] using hiB

theorem card_atomVertices_supportPartitionAtomFamily_eq_of_blocks {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hblocks : ∀ B : P.parts, atomVertices (blockAtoms B) = B.1) :
    (atomVertices (supportPartitionAtomFamily P blockAtoms)).card = S.card := by
  rw [atomVertices_supportPartitionAtomFamily_eq_of_blocks (q := q) P blockAtoms hblocks]

theorem supportPartitionAtomFamily_lift_eq_block_eq {S : Finset (Fin q)}
    (P : Finpartition S) {B C : P.parts} {A : Atom B.1} {A' : Atom C.1}
    (h : atom_mono (q := q) (P.subset B.2) A =
      atom_mono (q := q) (P.subset C.2) A') :
    B = C := by
  apply Subtype.ext
  have hleft : A.edge.1.1 = A'.edge.1.1 := by
    exact congrArg (fun atom : Atom S => atom.edge.1.1) h
  have hAleft : A.edge.1.1 ∈ B.1 := A.edge.2.1
  have hAleftC : A.edge.1.1 ∈ C.1 := by
    rw [hleft]
    exact A'.edge.2.1
  exact P.eq_of_mem_parts B.2 C.2 hAleft hAleftC

/-- The global atom rows of a support partition are exactly the disjoint union
of the block-local atom rows.  This is the row-indexing leaf needed for the
block-diagonal rank-sum theorem. -/
noncomputable def supportPartitionAtomFamilySigmaEquiv {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    (Σ B : P.parts, blockAtoms B) ≃ supportPartitionAtomFamily P blockAtoms :=
  Equiv.ofBijective
    (fun x : Σ B : P.parts, blockAtoms B =>
      ⟨atom_mono (P.subset x.1.2) x.2.1, by
        unfold supportPartitionAtomFamily
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨x.1, by simp, Finset.mem_image.mpr ⟨x.2.1, x.2.2, rfl⟩⟩⟩)
    ⟨by
      intro x y h
      cases x with
      | mk B A =>
        cases y with
        | mk C A' =>
          have hAtom : atom_mono (q := q) (P.subset B.2) A.1 =
              atom_mono (q := q) (P.subset C.2) A'.1 := by
            exact congrArg Subtype.val h
          have hBC : B = C := supportPartitionAtomFamily_lift_eq_block_eq (q := q) P hAtom
          subst hBC
          have hA : A.1 = A'.1 := atom_mono_injective (q := q) (P.subset B.2) hAtom
          cases A with
          | mk Aval Ah =>
            cases A' with
            | mk A'val A'h =>
              simp only at hA
              subst hA
              rfl,
     by
      intro z
      rcases z with ⟨atom, hmem⟩
      unfold supportPartitionAtomFamily at hmem
      rcases Finset.mem_biUnion.mp hmem with ⟨B, _hB, himg⟩
      rcases Finset.mem_image.mp himg with ⟨A, hA, hval⟩
      refine ⟨⟨B, ⟨A, hA⟩⟩, ?_⟩
      apply Subtype.ext
      simpa using hval⟩

theorem card_supportPartitionAtomFamily {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    Fintype.card (supportPartitionAtomFamily P blockAtoms) =
      ∑ B : P.parts, (blockAtoms B).card := by
  rw [← Fintype.card_congr (supportPartitionAtomFamilySigmaEquiv (q := q) P blockAtoms)]
  simp

instance atomFamilyHolds_decidable [AddGroup G] [DecidableEq G]
    (y a : Fin q → G) {S : Finset (Fin q)} (A : Finset (Atom S)) :
    Decidable (AtomFamilyHolds y a A) := by
  unfold AtomFamilyHolds
  infer_instance

/-- View a finite atom family as the row index type formed by its attached
members. -/
def atomFamilyRow {S : Finset (Fin q)} (A : Finset (Atom S)) : A → Atom S :=
  fun atom => atom.1

@[simp]
theorem atomFamilyRow_supportPartitionAtomFamilySigmaEquiv {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (x : Σ B : P.parts, blockAtoms B) :
    atomFamilyRow (supportPartitionAtomFamily P blockAtoms)
      (supportPartitionAtomFamilySigmaEquiv (q := q) P blockAtoms x) =
        atom_mono (P.subset x.1.2) x.2.1 := by
  rfl

/-- Sigma-indexed row for a support-partition atom family after reindexing the
global row set by `supportPartitionAtomFamilySigmaEquiv`. -/
def supportPartitionSigmaAtomRow {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    (Σ B : P.parts, blockAtoms B) → Atom S :=
  fun x => atom_mono (P.subset x.1.2) x.2.1

@[simp]
theorem hiddenConstraintMap_supportPartitionSigmaAtomRow_apply (K : Type*) [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (a : Fin q → K) :
    hiddenConstraintMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) a =
      fun x => hiddenConstraintMap (q := q) K (atomFamilyRow (blockAtoms x.1)) a x.2 := by
  funext x
  rfl

@[simp]
theorem visibleRhsMap_supportPartitionSigmaAtomRow_apply [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → K) :
    visibleRhsMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) y =
      fun x => visibleRhsMap (q := q) K (atomFamilyRow (blockAtoms x.1)) y x.2 := by
  funext x
  rfl

@[simp]
theorem jointConstraintMap_supportPartitionSigmaAtomRow_apply [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (ay : (Fin q → K) × (Fin q → K)) :
    jointConstraintMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) ay =
      fun x => jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms x.1)) ay x.2 := by
  funext x
  simp [jointConstraintMap_apply]

theorem jointRank_supportPartitionAtomFamily_eq_sigma [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    jointRank (q := q) K (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) =
      jointRank (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) := by
  let E : ((supportPartitionAtomFamily P blockAtoms) → K) ≃ₗ[K]
      ((Σ B : P.parts, blockAtoms B) → K) :=
    LinearEquiv.piCongrLeft K (fun _ : (Σ B : P.parts, blockAtoms B) => K)
      (supportPartitionAtomFamilySigmaEquiv (q := q) P blockAtoms).symm
  let Lg := jointConstraintMap (q := q) K
    (atomFamilyRow (supportPartitionAtomFamily P blockAtoms))
  let Ls := jointConstraintMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms)
  have hE_apply : ∀ ay, E (Lg ay) = Ls ay := by
    intro ay
    funext x
    simp [E, Ls, Lg, jointConstraintMap_apply, LinearEquiv.piCongrLeft, atomFamilyRow,
      supportPartitionAtomFamilySigmaEquiv]
  have hmap : (LinearMap.range Lg).map (E : _ →ₗ[K] _) = LinearMap.range Ls := by
    ext z
    constructor
    · rintro ⟨_w, ⟨ay, rfl⟩, rfl⟩
      exact ⟨ay, (hE_apply ay).symm⟩
    · rintro ⟨ay, rfl⟩
      exact ⟨Lg ay, ⟨ay, rfl⟩, hE_apply ay⟩
  unfold jointRank
  dsimp [Lg, Ls] at hmap
  rw [← LinearEquiv.finrank_map_eq E (LinearMap.range (jointConstraintMap (q := q) K
    (atomFamilyRow (supportPartitionAtomFamily P blockAtoms))))]
  rw [hmap]

theorem jointRank_supportPartitionAtomFamily_ge_sum_of_sigma_rank_sum [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hrank_sigma : (∑ B : P.parts,
      jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
        jointRank (q := q) K (supportPartitionSigmaAtomRow P blockAtoms)) :
    (∑ B : P.parts,
      jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
        jointRank (q := q) K
          (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) := by
  rwa [jointRank_supportPartitionAtomFamily_eq_sigma (q := q) (K := K) P blockAtoms]

/-- Curried block form of the sigma-indexed support-partition joint constraint
map.  The remaining rank-additivity proof must show that this map has range
equal to the product of the block-local ranges. -/
def supportPartitionCurriedJointConstraintMap [Field K] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    ((Fin q → K) × (Fin q → K)) →ₗ[K]
      (∀ B : P.parts, blockAtoms B → K) :=
  (LinearEquiv.piCurry K (fun B (_ : blockAtoms B) => K)).toLinearMap.comp
    (jointConstraintMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms))

@[simp]
theorem supportPartitionCurriedJointConstraintMap_apply [Field K] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (ay : (Fin q → K) × (Fin q → K)) :
    supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms ay =
      fun B => jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)) ay := by
  funext B atom
  rfl

/-- Assemble a global tuple from one tuple on each block of a support
partition, filling coordinates outside the partition support with zero. -/
noncomputable def supportPartitionAssemble [Zero K] {S : Finset (Fin q)} (P : Finpartition S)
    (v : ∀ B : P.parts, B.1 → K) : Fin q → K :=
  fun i => if hi : i ∈ S then
    v ⟨P.part i, P.part_mem.mpr hi⟩ ⟨i, (P.mem_part_self.mpr hi)⟩
  else 0

@[simp]
theorem supportPartitionAssemble_eq_of_mem [Zero K] {S : Finset (Fin q)} (P : Finpartition S)
    (v : ∀ B : P.parts, B.1 → K) {B : P.parts} {i : Fin q}
    (hi : i ∈ B.1) :
    supportPartitionAssemble (K := K) P v i = v B ⟨i, hi⟩ := by
  unfold supportPartitionAssemble
  have hiS : i ∈ S := P.subset B.2 hi
  simp [hiS]
  cases B with
  | mk Bval hB =>
    have hi' : i ∈ Bval := by simpa using hi
    have hpart : P.part i = Bval := P.part_eq_of_mem hB hi'
    subst hpart
    rfl

/-- Assemble a global tuple from outside-support coordinates and one tuple on
each block of a support partition. -/
noncomputable def supportPartitionAssembleWithOutside {K : Type*}
    {S : Finset (Fin q)} (P : Finpartition S)
    (outside : {i : Fin q // i ∉ S} → K)
    (v : ∀ B : P.parts, B.1 → K) : Fin q → K :=
  fun i => if hi : i ∈ S then
    v ⟨P.part i, P.part_mem.mpr hi⟩ ⟨i, (P.mem_part_self.mpr hi)⟩
  else outside ⟨i, hi⟩

@[simp]
theorem supportPartitionAssembleWithOutside_eq_of_mem {K : Type*}
    {S : Finset (Fin q)} (P : Finpartition S)
    (outside : {i : Fin q // i ∉ S} → K)
    (v : ∀ B : P.parts, B.1 → K) {B : P.parts} {i : Fin q}
    (hi : i ∈ B.1) :
    supportPartitionAssembleWithOutside (q := q) P outside v i = v B ⟨i, hi⟩ := by
  unfold supportPartitionAssembleWithOutside
  have hiS : i ∈ S := P.subset B.2 hi
  simp [hiS]
  cases B with
  | mk Bval hB =>
    have hi' : i ∈ Bval := by simpa using hi
    have hpart : P.part i = Bval := P.part_eq_of_mem hB hi'
    subst hpart
    rfl

@[simp]
theorem supportPartitionAssembleWithOutside_eq_of_not_mem {K : Type*}
    {S : Finset (Fin q)} (P : Finpartition S)
    (outside : {i : Fin q // i ∉ S} → K)
    (v : ∀ B : P.parts, B.1 → K) {i : Fin q}
    (hi : i ∉ S) :
    supportPartitionAssembleWithOutside (q := q) P outside v i = outside ⟨i, hi⟩ := by
  simp [supportPartitionAssembleWithOutside, hi]

/-- A global tuple is equivalently an outside-support tuple plus one tuple on each
block of a support partition. -/
noncomputable def supportPartitionAssignmentEquiv {K : Type*}
    {S : Finset (Fin q)} (P : Finpartition S) :
    ({i : Fin q // i ∉ S} → K) × (∀ B : P.parts, B.1 → K) ≃ (Fin q → K) where
  toFun x := supportPartitionAssembleWithOutside (q := q) P x.1 x.2
  invFun a :=
    (fun i => a i.1, fun B i => a i.1)
  left_inv := by
    intro x
    rcases x with ⟨outside, v⟩
    apply Prod.ext
    · funext i
      exact supportPartitionAssembleWithOutside_eq_of_not_mem
        (q := q) P outside v i.2
    · funext B i
      exact supportPartitionAssembleWithOutside_eq_of_mem
        (q := q) P outside v i.2
  right_inv := by
    intro a
    funext i
    by_cases hi : i ∈ S
    · unfold supportPartitionAssembleWithOutside
      simp [hi]
    · exact supportPartitionAssembleWithOutside_eq_of_not_mem
        (q := q) P (fun i : {i : Fin q // i ∉ S} => a i.1)
        (fun B i => a i.1) hi

theorem card_supportPartitionAssignmentProduct (K : Type*) [Fintype K]
    {S : Finset (Fin q)} (P : Finpartition S) :
    Fintype.card (({i : Fin q // i ∉ S} → K) × (∀ B : P.parts, B.1 → K)) =
      Fintype.card (Fin q → K) := by
  exact Fintype.card_congr (supportPartitionAssignmentEquiv (q := q) (K := K) P)

/-- Lift an assignment on a finite support to the full coordinate set, using
zero off support.  Atom families over that support are insensitive to the
chosen off-support value. -/
noncomputable def supportSubtypeLift [Zero K] {S : Finset (Fin q)}
    (aS : S → K) : Fin q → K :=
  fun i => if hi : i ∈ S then aS ⟨i, hi⟩ else 0

@[simp]
theorem supportSubtypeLift_eq_of_mem [Zero K] {S : Finset (Fin q)}
    (aS : S → K) {i : Fin q} (hi : i ∈ S) :
    supportSubtypeLift (q := q) aS i = aS ⟨i, hi⟩ := by
  simp [supportSubtypeLift, hi]

/-- Local satisfaction for an atom family whose hidden assignment is only
defined on the atom support. -/
def AtomFamilyHoldsOn [AddGroup G] (y : Fin q → G) {S : Finset (Fin q)}
    (A : Finset (Atom S)) (aS : S → G) : Prop :=
  AtomFamilyHolds y (supportSubtypeLift (q := q) aS) A

instance atomFamilyHoldsOn_decidable [AddGroup G] [DecidableEq G]
    (y : Fin q → G) {S : Finset (Fin q)} (A : Finset (Atom S)) (aS : S → G) :
    Decidable (AtomFamilyHoldsOn (q := q) y A aS) := by
  unfold AtomFamilyHoldsOn
  infer_instance

theorem atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support
    [AddGroup G] [DecidableEq G] {S : Finset (Fin q)}
    (A : Finset (Atom S)) (y : Fin q → G) (a : Fin q → G) (aS : S → G)
    (h : ∀ i (hi : i ∈ S), a i = aS ⟨i, hi⟩) :
    AtomFamilyHolds y a A ↔ AtomFamilyHoldsOn (q := q) y A aS := by
  unfold AtomFamilyHoldsOn
  exact atomFamilyHolds_congr_on_support (q := q) (G := G)
    (fun i hi => by
      rw [supportSubtypeLift_eq_of_mem (q := q) aS hi]
      exact h i hi)

theorem atomFamilyHolds_supportPartitionAssembleWithOutside_iff
    [AddGroup G] [DecidableEq G] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → G) (outside : {i : Fin q // i ∉ S} → G)
    (v : ∀ B : P.parts, B.1 → G) :
    AtomFamilyHolds y (supportPartitionAssembleWithOutside (q := q) P outside v)
        (supportPartitionAtomFamily P blockAtoms) ↔
      ∀ B : P.parts, AtomFamilyHoldsOn (q := q) y (blockAtoms B) (v B) := by
  rw [atomFamilyHolds_supportPartitionAtomFamily_iff]
  constructor
  · intro h B
    exact (atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support
      (q := q) (G := G) (blockAtoms B) y
      (supportPartitionAssembleWithOutside (q := q) P outside v) (v B)
      (fun i hi => supportPartitionAssembleWithOutside_eq_of_mem (q := q) P outside v hi)).mp
      (h B)
  · intro h B
    exact (atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support
      (q := q) (G := G) (blockAtoms B) y
      (supportPartitionAssembleWithOutside (q := q) P outside v) (v B)
      (fun i hi => supportPartitionAssembleWithOutside_eq_of_mem (q := q) P outside v hi)).mpr
      (h B)

/-- Hidden-fiber assembly over a support partition.  A global hidden assignment
for the lifted union of block atom families is equivalent to arbitrary
off-support coordinates together with one satisfying hidden assignment on each
block. -/
noncomputable def supportPartitionAtomFamilyHiddenFiberEquiv
    [AddGroup G] [DecidableEq G] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → G) :
    (({i : Fin q // i ∉ S} → G) ×
      {v : (B : P.parts) → B.1 → G //
        ∀ B : P.parts, AtomFamilyHoldsOn (q := q) y (blockAtoms B) (v B)}) ≃
      {a : Fin q → G //
        AtomFamilyHolds y a (supportPartitionAtomFamily P blockAtoms)} where
  toFun x :=
    ⟨supportPartitionAssembleWithOutside (q := q) P x.1 x.2.1,
      (atomFamilyHolds_supportPartitionAssembleWithOutside_iff
        (q := q) (G := G) P blockAtoms y x.1 x.2.1).mpr x.2.2⟩
  invFun a :=
    (fun i : {i : Fin q // i ∉ S} => a.1 i.1,
      ⟨fun B i => a.1 i.1, by
        intro B
        have hblock : AtomFamilyHolds y a.1 (blockAtoms B) :=
          (atomFamilyHolds_supportPartitionAtomFamily_iff (q := q) (G := G)
            P blockAtoms y a.1).mp a.2 B
        exact (atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support
          (q := q) (G := G) (blockAtoms B) y a.1 (fun i : B.1 => a.1 i.1)
          (fun i hi => rfl)).mp hblock⟩)
  left_inv := by
    intro x
    rcases x with ⟨outside, v, hv⟩
    apply Prod.ext
    · funext i
      exact supportPartitionAssembleWithOutside_eq_of_not_mem
        (q := q) P outside v i.2
    · apply Subtype.ext
      funext B i
      exact supportPartitionAssembleWithOutside_eq_of_mem
        (q := q) P outside v i.2
  right_inv := by
    intro a
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · unfold supportPartitionAssembleWithOutside
      simp [hi]
    · exact supportPartitionAssembleWithOutside_eq_of_not_mem
        (q := q) P (fun i : {i : Fin q // i ∉ S} => a.1 i.1)
        (fun B i => a.1 i.1) hi

/-- The subtype of block assignments satisfying every block atom family is the
dependent product of the individual block hidden fibers. -/
noncomputable def supportPartitionBlockHiddenFiberEquiv
    [AddGroup G] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → G) :
    {v : (B : P.parts) → B.1 → G //
      ∀ B : P.parts, AtomFamilyHoldsOn (q := q) y (blockAtoms B) (v B)} ≃
      (∀ B : P.parts,
        {aB : B.1 → G // AtomFamilyHoldsOn (q := q) y (blockAtoms B) aB}) where
  toFun v B := ⟨v.1 B, v.2 B⟩
  invFun v := ⟨fun B => (v B).1, fun B => (v B).2⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext B
    rfl
  right_inv := by
    intro v
    funext B
    apply Subtype.ext
    rfl

theorem card_supportPartition_blockHiddenFiber
    [AddGroup G] [DecidableEq G] [Fintype G] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → G) :
    Fintype.card {v : (B : P.parts) → B.1 → G //
      ∀ B : P.parts, AtomFamilyHoldsOn (q := q) y (blockAtoms B) (v B)} =
      ∏ B : P.parts,
        Fintype.card {aB : B.1 → G //
          AtomFamilyHoldsOn (q := q) y (blockAtoms B) aB} := by
  rw [Fintype.card_congr
    (supportPartitionBlockHiddenFiberEquiv (q := q) (G := G) P blockAtoms y)]
  exact Fintype.card_pi

theorem card_supportPartitionAtomFamily_hiddenFiber_eq_outside_mul_prod_blocks
    [AddGroup G] [DecidableEq G] [Fintype G] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → G) :
    Fintype.card {a : Fin q → G //
        AtomFamilyHolds y a (supportPartitionAtomFamily P blockAtoms)} =
      Fintype.card ({i : Fin q // i ∉ S} → G) *
        ∏ B : P.parts,
          Fintype.card {aB : B.1 → G //
            AtomFamilyHoldsOn (q := q) y (blockAtoms B) aB} := by
  rw [Fintype.card_congr
    (supportPartitionAtomFamilyHiddenFiberEquiv (q := q) (G := G) P blockAtoms y).symm]
  rw [Fintype.card_prod]
  rw [card_supportPartition_blockHiddenFiber (q := q) (G := G) P blockAtoms y]

/-- Real-valued form of the support-partition hidden-fiber count assembly.  The
product of block-local hidden fibers equals the global hidden fiber divided by
the freely chosen off-support coordinates. -/
theorem prod_blockHiddenFiber_card_eq_global_div_outside_real
    [AddGroup G] [DecidableEq G] [Fintype G] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (y : Fin q → G) :
    (∏ B : P.parts,
      (Fintype.card {aB : B.1 → G //
        AtomFamilyHoldsOn (q := q) y (blockAtoms B) aB} : ℝ)) =
      (Fintype.card {a : Fin q → G //
        AtomFamilyHolds y a (supportPartitionAtomFamily P blockAtoms)} : ℝ) /
        (Fintype.card ({i : Fin q // i ∉ S} → G) : ℝ) := by
  have hcard := card_supportPartitionAtomFamily_hiddenFiber_eq_outside_mul_prod_blocks
    (q := q) (G := G) P blockAtoms y
  have hcardR :
      (Fintype.card {a : Fin q → G //
        AtomFamilyHolds y a (supportPartitionAtomFamily P blockAtoms)} : ℝ) =
        (Fintype.card ({i : Fin q // i ∉ S} → G) : ℝ) *
          ∏ B : P.parts,
            (Fintype.card {aB : B.1 → G //
              AtomFamilyHoldsOn (q := q) y (blockAtoms B) aB} : ℝ) := by
    exact_mod_cast hcard
  have houtside_ne :
      (Fintype.card ({i : Fin q // i ∉ S} → G) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := {i : Fin q // i ∉ S} → G)).ne'
  rw [hcardR]
  field_simp [houtside_ne]

/-- Build the global support-partition hidden-fiber evaluation from block-local
hidden-fiber evaluations.  The coefficient pays the inverse of the free
outside-support assignment count, as required by
`prod_blockHiddenFiber_card_eq_global_div_outside_real`. -/
theorem supportPartitionClusterProductContribution_eq_sum_pi_blockLocalAtomized
    [Field K] [Fintype K] [DecidableEq K]
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (BlockTerm : {S : Finset (Fin q)} → PairCluster S → Type*)
    [blockTermFintype : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      Fintype (BlockTerm C)]
    (blockCoeff : ∀ {S : Finset (Fin q)} (C : PairCluster S), BlockTerm C → ℝ)
    (blockAtoms : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      BlockTerm C → Finset (Atom S))
    (hblockEval : ∀ {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → K),
      blockContribution S C y =
        ∑ tB : BlockTerm C,
          blockCoeff C tB *
            (Fintype.card {aS : S → K //
              AtomFamilyHoldsOn (q := q) y (blockAtoms C tB) aS} : ℝ))
    {S : Finset (Fin q)} (idx : Mayer.SupportPartitionClusters (q := q) S)
    (y : Fin q → K) :
    Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
        blockContribution S idx y =
      ∑ t : (B : idx.1.parts) → BlockTerm (idx.2 B),
        ((∏ B : idx.1.parts, blockCoeff (idx.2 B) (t B)) /
            (Fintype.card ({i : Fin q // i ∉ S} → K) : ℝ)) *
          (Fintype.card {a : Fin q → K //
            AtomFamilyHolds y a
              (supportPartitionAtomFamily idx.1
                (fun B : idx.1.parts => blockAtoms (idx.2 B) (t B)))} : ℝ) := by
  classical
  rw [RandomSystems.Applications.XoP.Mayer.supportPartitionClusterProductContribution_eq_sum_pi_blockCoeff_mul_values
    (G := K) (q := q) blockContribution
    (fun {_S} idx B => BlockTerm (idx.2 B))
    (fun idx B tB => blockCoeff (idx.2 B) tB)
    (fun idx B tB y =>
      (Fintype.card {aS : B.1 → K //
        AtomFamilyHoldsOn (q := q) y (blockAtoms (idx.2 B) tB) aS} : ℝ))
    (by
      intro S' idx' B y'
      exact hblockEval (idx'.2 B) y')
    idx y]
  refine Finset.sum_congr rfl ?_
  intro t _ht
  have hcount := prod_blockHiddenFiber_card_eq_global_div_outside_real
    (q := q) (G := K) idx.1
    (fun B : idx.1.parts => blockAtoms (idx.2 B) (t B)) y
  rw [hcount]
  ring

/-- Local indicator sums over support assignments are support-local hidden-fiber
cardinalities.  This is the block-local analogue of
`sum_atomFamilyHolds_indicator_eq_card`, forced by the signed pair-Mayer block
contribution below. -/
theorem sum_atomFamilyHoldsOn_indicator_eq_card [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (A : Finset (Atom S)) (y : Fin q → G) :
    (∑ aS : S → G, if AtomFamilyHoldsOn (q := q) y A aS then (1 : ℝ) else 0) =
      (Fintype.card {aS : S → G // AtomFamilyHoldsOn (q := q) y A aS} : ℝ) := by
  simpa using (Fintype.card_subtype
    (fun aS : S → G => AtomFamilyHoldsOn (q := q) y A aS)).symm

/-- A full hidden assignment for atoms over support `S` is the same as an
arbitrary outside-support assignment plus a satisfying local assignment on
`S`. -/
noncomputable def atomFamilyLocalHiddenFiberEquiv
    [AddGroup G] [DecidableEq G] {S : Finset (Fin q)}
    (A : Finset (Atom S)) (y : Fin q → G) :
    (({i : Fin q // i ∉ S} → G) ×
      {aS : S → G // AtomFamilyHoldsOn (q := q) y A aS}) ≃
      {a : Fin q → G // AtomFamilyHolds y a A} where
  toFun x :=
    ⟨(fun i => if hi : i ∈ S then x.2.1 ⟨i, hi⟩ else x.1 ⟨i, hi⟩),
      (atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support
        (q := q) (G := G) A y
        (fun i => if hi : i ∈ S then x.2.1 ⟨i, hi⟩ else x.1 ⟨i, hi⟩)
        x.2.1
        (fun i hi => by simp [hi])).mpr x.2.2⟩
  invFun a :=
    (fun i : {i : Fin q // i ∉ S} => a.1 i.1,
      ⟨fun i : S => a.1 i.1,
        (atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support
          (q := q) (G := G) A y a.1 (fun i : S => a.1 i.1)
          (fun _i _hi => rfl)).mp a.2⟩)
  left_inv := by
    intro x
    rcases x with ⟨outside, aS, haS⟩
    apply Prod.ext
    · funext i
      simp [i.2]
    · apply Subtype.ext
      funext i
      simp [i.2]
  right_inv := by
    intro a
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S <;> simp [hi]

/-- Cardinality form of `atomFamilyLocalHiddenFiberEquiv`. -/
theorem card_atomFamily_hiddenFiber_eq_outside_mul_local
    [AddGroup G] [DecidableEq G] [Fintype G] {S : Finset (Fin q)}
    (A : Finset (Atom S)) (y : Fin q → G) :
    Fintype.card {a : Fin q → G // AtomFamilyHolds y a A} =
      Fintype.card ({i : Fin q // i ∉ S} → G) *
        Fintype.card {aS : S → G // AtomFamilyHoldsOn (q := q) y A aS} := by
  rw [Fintype.card_congr
    (atomFamilyLocalHiddenFiberEquiv (q := q) (G := G) A y).symm]
  rw [Fintype.card_prod]

theorem range_supportPartitionCurriedJointConstraintMap_le_pi_block_ranges [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    LinearMap.range (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms) ≤
      Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)))) := by
  rintro _z ⟨ay, rfl⟩
  intro B _hB
  exact ⟨ay, by ext atom; rfl⟩

theorem pi_block_ranges_le_range_supportPartitionCurriedJointConstraintMap [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)))) ≤
      LinearMap.range (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms) := by
  classical
  intro z hz
  have hz' : ∀ B : P.parts, z B ∈
      LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B))) := by
    intro B
    exact hz B trivial
  choose ay hay using hz'
  let a : Fin q → K := supportPartitionAssemble (K := K) P (fun B i => (ay B).1 i.1)
  let y : Fin q → K := supportPartitionAssemble (K := K) P (fun B i => (ay B).2 i.1)
  refine ⟨(a, y), ?_⟩
  funext B atom
  have hB := congrFun (hay B) atom
  rw [← hB]
  cases atom with
  | mk A hA =>
    cases A with
    | mk e c =>
      cases c
      · simp [jointConstraintMap_apply, hiddenConstraintMap_apply, visibleRhsMap_apply,
          atomFamilyRow, atomLinearForm, atomRhs, edgeDifferenceLinearForm, a, y]
        rw [supportPartitionAssemble_eq_of_mem (K := K) P
            (fun B i => (ay B).1 i.1) e.2.1,
          supportPartitionAssemble_eq_of_mem (K := K) P
            (fun B i => (ay B).1 i.1) e.2.2.1]
      · simp [jointConstraintMap_apply, hiddenConstraintMap_apply, visibleRhsMap_apply,
          atomFamilyRow, atomLinearForm, atomRhs, edgeDifferenceLinearForm, a, y]
        rw [supportPartitionAssemble_eq_of_mem (K := K) P
            (fun B i => (ay B).1 i.1) e.2.1,
          supportPartitionAssemble_eq_of_mem (K := K) P
            (fun B i => (ay B).1 i.1) e.2.2.1,
          supportPartitionAssemble_eq_of_mem (K := K) P
            (fun B i => (ay B).2 i.1) e.2.1,
          supportPartitionAssemble_eq_of_mem (K := K) P
            (fun B i => (ay B).2 i.1) e.2.2.1]

theorem range_supportPartitionCurriedJointConstraintMap_eq_pi_block_ranges [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    LinearMap.range (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms) =
      Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)))) := by
  exact le_antisymm
    (range_supportPartitionCurriedJointConstraintMap_le_pi_block_ranges
      (q := q) (K := K) P blockAtoms)
    (pi_block_ranges_le_range_supportPartitionCurriedJointConstraintMap
      (q := q) (K := K) P blockAtoms)

theorem finrank_pi_block_joint_ranges [Field K] {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    Module.finrank K (Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B))))) =
      ∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B)) := by
  let p : (B : P.parts) → Submodule K (blockAtoms B → K) := fun B =>
    LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)))
  let E : (Submodule.pi Set.univ p) ≃ₗ[K] (∀ B : P.parts, p B) :=
    { toFun := fun x B => ⟨x.1 B, x.2 B trivial⟩
      invFun := fun y => ⟨fun B => (y B).1, fun B _ => (y B).2⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  calc
    Module.finrank K (Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B))))) =
        Module.finrank K (∀ B : P.parts, p B) := by
          exact LinearEquiv.finrank_eq E
    _ = ∑ B : P.parts, Module.finrank K (p B) := by
          simpa using (Module.finrank_pi_fintype (R := K) (M := fun B : P.parts => p B))
    _ = ∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B)) := by
          rfl

theorem jointRank_supportPartitionSigmaAtomRow_eq_curried [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    jointRank (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) =
      Module.finrank K (LinearMap.range
        (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms)) := by
  let E : (((Σ B : P.parts, blockAtoms B) → K) ≃ₗ[K]
      (∀ B : P.parts, blockAtoms B → K)) :=
    LinearEquiv.piCurry K (fun B (_ : blockAtoms B) => K)
  let Ls := jointConstraintMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms)
  have hrange : LinearMap.range
      (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms) =
        (LinearMap.range Ls).map (E : _ →ₗ[K] _) := by
    ext z
    constructor
    · rintro ⟨ay, rfl⟩
      exact ⟨Ls ay, ⟨ay, rfl⟩, rfl⟩
    · rintro ⟨_w, ⟨ay, rfl⟩, rfl⟩
      exact ⟨ay, rfl⟩
  unfold jointRank
  dsimp [Ls] at hrange
  rw [hrange]
  exact (LinearEquiv.finrank_map_eq E (LinearMap.range
    (jointConstraintMap (q := q) K (supportPartitionSigmaAtomRow P blockAtoms)))).symm

theorem jointRank_supportPartitionSigmaAtomRow_ge_sum_of_pi_le_range [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hpi_le : Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)))) ≤
      LinearMap.range (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms)) :
    (∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
      jointRank (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) := by
  rw [jointRank_supportPartitionSigmaAtomRow_eq_curried (q := q) (K := K) P blockAtoms]
  rw [← finrank_pi_block_joint_ranges (q := q) (K := K) P blockAtoms]
  exact Submodule.finrank_mono hpi_le

theorem jointRank_supportPartitionAtomFamily_ge_sum_of_pi_le_range [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hpi_le : Submodule.pi Set.univ (fun B : P.parts =>
        LinearMap.range (jointConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)))) ≤
      LinearMap.range (supportPartitionCurriedJointConstraintMap (q := q) (K := K) P blockAtoms)) :
    (∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
      jointRank (q := q) K
        (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) := by
  exact jointRank_supportPartitionAtomFamily_ge_sum_of_sigma_rank_sum (q := q) (K := K)
    P blockAtoms
    (jointRank_supportPartitionSigmaAtomRow_ge_sum_of_pi_le_range (q := q) (K := K)
      P blockAtoms hpi_le)

theorem jointRank_supportPartitionSigmaAtomRow_ge_sum [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    (∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
      jointRank (q := q) K (supportPartitionSigmaAtomRow P blockAtoms) := by
  exact jointRank_supportPartitionSigmaAtomRow_ge_sum_of_pi_le_range (q := q) (K := K)
    P blockAtoms
    (pi_block_ranges_le_range_supportPartitionCurriedJointConstraintMap
      (q := q) (K := K) P blockAtoms)

theorem jointRank_supportPartitionAtomFamily_ge_sum [Field K]
    {S : Finset (Fin q)}
    (P : Finpartition S) (blockAtoms : (B : P.parts) → Finset (Atom B.1)) :
    (∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
      jointRank (q := q) K (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) := by
  exact jointRank_supportPartitionAtomFamily_ge_sum_of_pi_le_range (q := q) (K := K)
    P blockAtoms
    (pi_block_ranges_le_range_supportPartitionCurriedJointConstraintMap
      (q := q) (K := K) P blockAtoms)

theorem atomFamilyHolds_iff_forall_atomFamilyRow [AddGroup G]
    (y a : Fin q → G) {S : Finset (Fin q)} (A : Finset (Atom S)) :
    AtomFamilyHolds y a A ↔ ∀ atom : A, atomHolds y a (atomFamilyRow A atom) := by
  constructor
  · intro h atom
    exact h atom.1 atom.2
  · intro h atom hatom
    exact h ⟨atom, hatom⟩

/-- Atom-family satisfaction is exactly the corresponding finite row-family
linear system. -/
theorem atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap [Field K]
    (y a : Fin q → K) {S : Finset (Fin q)} (A : Finset (Atom S)) :
    AtomFamilyHolds y a A ↔
      hiddenConstraintMap (q := q) K (atomFamilyRow A) a =
        visibleRhsMap (q := q) K (atomFamilyRow A) y := by
  rw [atomFamilyHolds_iff_forall_atomFamilyRow]
  exact all_atomHolds_iff_hiddenConstraintMap_eq_visibleRhsMap (K := K)
    (atomFamilyRow A) y a

/-- Cardinality of hidden assignments satisfying a feasible selected atom
family.  This is the first concrete bridge from post-pair atomization to the
rank/codimension counting API. -/
theorem atomFamily_solution_card_eq_pow_of_feasible [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) (y : Fin q → K)
    (hfeas : ∃ a : Fin q → K, AtomFamilyHolds y a A) :
    Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} =
      Fintype.card K ^ (q - hiddenRank (q := q) K (atomFamilyRow A)) := by
  let row := atomFamilyRow A
  have hfeas' : ∃ a : Fin q → K,
      hiddenConstraintMap (q := q) K row a = visibleRhsMap (q := q) K row y := by
    rcases hfeas with ⟨a, ha⟩
    exact ⟨a, (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
      (K := K) y a A).mp ha⟩
  let E1 := {a : Fin q → K // AtomFamilyHolds y a A}
  let E2 := {a : Fin q → K //
    hiddenConstraintMap (q := q) K row a = visibleRhsMap (q := q) K row y}
  have hcard_eq : Fintype.card E1 = Fintype.card E2 := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun a => ⟨a.1,
          (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
            (K := K) y a.1 A).mp a.2⟩
        invFun := fun a => ⟨a.1,
          (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
            (K := K) y a.1 A).mpr a.2⟩
        left_inv := by
          intro a
          rfl
        right_inv := by
          intro a
          rfl }
  rw [hcard_eq]
  exact hiddenSolutionFiber_card_eq_pow_of_feasible (q := q) (K := K) row y hfeas'

/-- If a selected atom family is feasible for every visible transcript, then
all full hidden-solution fibers have the same cardinality. -/
theorem atomFamily_solution_card_eq_of_forall_feasible
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S))
    (hfeas : ∀ y : Fin q → K, ∃ a : Fin q → K, AtomFamilyHolds y a A)
    (y y' : Fin q → K) :
    Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} =
      Fintype.card {a : Fin q → K // AtomFamilyHolds y' a A} := by
  rw [atomFamily_solution_card_eq_pow_of_feasible (q := q) (K := K) A y (hfeas y)]
  rw [atomFamily_solution_card_eq_pow_of_feasible (q := q) (K := K) A y' (hfeas y')]

/-- Atom-family satisfaction is the kernel event for the joint hidden/visible
constraint map.  This is the XoP-specific glue needed by the fixed-bond
codimension count below; the linear algebra in that count reuses Mathlib's
rank-nullity and finite-vector-space cardinality theorems. -/
theorem atomFamilyHolds_iff_jointConstraintMap_eq_zero [Field K]
    (y a : Fin q → K) {S : Finset (Fin q)} (A : Finset (Atom S)) :
    AtomFamilyHolds y a A ↔
      jointConstraintMap (q := q) K (atomFamilyRow A) (a, y) = 0 := by
  rw [atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap (K := K) y a A]
  constructor
  · intro h
    ext atom
    simp [jointConstraintMap_apply, h]
  · intro h
    have hfun := congrFun h
    funext atom
    have := hfun atom
    simpa [jointConstraintMap_apply, sub_eq_zero] using this

/-- Fixed-bond codimension count for selected atom families.

This is the concrete parent theorem for the rank/codimension route: a selected
atom family cuts out a linear kernel in the joint `(a, y)` space, with
codimension equal to `jointRank`. -/
theorem atomFamily_joint_card_eq_pow [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) :
    Fintype.card { ay : (Fin q → K) × (Fin q → K) //
      AtomFamilyHolds ay.2 ay.1 A } =
      Fintype.card K ^ (2 * q - jointRank (q := q) K (atomFamilyRow A)) := by
  let L := jointConstraintMap (q := q) K (atomFamilyRow A)
  let E1 := { ay : (Fin q → K) × (Fin q → K) // AtomFamilyHolds ay.2 ay.1 A }
  let E2 := LinearMap.ker L
  letI : Fintype E2 := Fintype.ofFinite E2
  have hcard_eq : Fintype.card E1 = Fintype.card E2 := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ay => ⟨ay.1,
          (atomFamilyHolds_iff_jointConstraintMap_eq_zero
            (K := K) ay.1.2 ay.1.1 A).mp ay.2⟩
        invFun := fun ay => ⟨ay.1,
          (atomFamilyHolds_iff_jointConstraintMap_eq_zero
            (K := K) ay.1.2 ay.1.1 A).mpr ay.2⟩
        left_inv := by
          intro ay
          rfl
        right_inv := by
          intro ay
          rfl }
  have hker_card :
      Fintype.card E2 = Fintype.card K ^ Module.finrank K E2 := by
    exact Module.card_eq_pow_finrank (K := K) (V := E2)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdom : Module.finrank K ((Fin q → K) × (Fin q → K)) = 2 * q := by
    simp [Module.finrank_prod]
    omega
  have hsum' :
      jointRank (q := q) K (atomFamilyRow A) + Module.finrank K E2 = 2 * q := by
    dsimp [jointRank, E2, L]
    simpa [hdom] using hsum
  have hker_rank :
      Module.finrank K E2 = 2 * q - jointRank (q := q) K (atomFamilyRow A) := by
    omega
  rw [hcard_eq, hker_card, hker_rank]

/-- The joint rank is bounded by the ambient joint hidden/visible dimension.
This is the ambient-dimension side condition needed to rewrite the fixed-bond
codimension count as an inverse power. -/
theorem jointRank_le_two_mul_q [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) :
    jointRank (q := q) K (atomFamilyRow A) ≤ 2 * q := by
  unfold jointRank
  have hle := LinearMap.finrank_range_le
    (jointConstraintMap (q := q) K (atomFamilyRow A))
  have hdom : Module.finrank K ((Fin q → K) × (Fin q → K)) = 2 * q := by
    simp [Module.finrank_prod]
    omega
  exact hle.trans_eq hdom

/-- Normalized form of `atomFamily_joint_card_eq_pow`, before cancelling the
ambient factor. -/
theorem atomFamily_joint_card_density_eq_pow_div_pow [Field K] [Fintype K]
    [DecidableEq K] {S : Finset (Fin q)} (A : Finset (Atom S)) :
    ((Fintype.card { ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 A } : NNReal) /
      (Fintype.card ((Fin q → K) × (Fin q → K)) : NNReal)) =
      (Fintype.card K : NNReal) ^ (2 * q - jointRank (q := q) K (atomFamilyRow A)) /
        (Fintype.card K : NNReal) ^ (2 * q) := by
  have hcard := atomFamily_joint_card_eq_pow (q := q) (K := K) A
  have hambient :
      Fintype.card ((Fin q → K) × (Fin q → K)) = Fintype.card K ^ (2 * q) := by
    rw [Fintype.card_prod]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [← pow_add]
    congr 1
    omega
  rw [hcard, hambient]
  norm_num

/-- Fixed-bond codimension probability: under the uniform joint `(a, y)` law, a
selected atom family occurs with exact mass `|K|^{-jointRank}`. -/
theorem atomFamily_joint_card_density_eq_inv_pow [Field K] [Fintype K]
    [DecidableEq K] {S : Finset (Fin q)} (A : Finset (Atom S)) :
    ((Fintype.card { ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 A } : NNReal) /
      (Fintype.card ((Fin q → K) × (Fin q → K)) : NNReal)) =
      1 / (Fintype.card K : NNReal) ^ jointRank (q := q) K (atomFamilyRow A) := by
  have hfrac := atomFamily_joint_card_density_eq_pow_div_pow (q := q) (K := K) A
  rw [hfrac]
  let n := 2 * q
  let r := jointRank (q := q) K (atomFamilyRow A)
  have hr : r ≤ n := jointRank_le_two_mul_q (q := q) (K := K) A
  have hbase : (Fintype.card K : NNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := K)).ne'
  have hpow : (Fintype.card K : NNReal) ^ n =
      (Fintype.card K : NNReal) ^ (n - r) *
        (Fintype.card K : NNReal) ^ r := by
    calc
      (Fintype.card K : NNReal) ^ n =
          (Fintype.card K : NNReal) ^ ((n - r) + r) := by
            rw [Nat.sub_add_cancel hr]
      _ = (Fintype.card K : NNReal) ^ (n - r) *
          (Fintype.card K : NNReal) ^ r := by
            rw [pow_add]
  rw [show 2 * q = n by rfl,
    show jointRank (q := q) K (atomFamilyRow A) = r by rfl]
  rw [hpow]
  field_simp [hbase]

/-- Each hidden row form is in the range of the dual hidden-constraint map.

This is the row-space bridge needed for graph rank lower bounds.  The rank
comparison itself reuses Mathlib's finite-dimensional dual-map rank theorem. -/
theorem atomLinearForm_mem_hidden_dualMap_range [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S) (r : ρ) :
    atomLinearForm (q := q) K (row r) ∈
      LinearMap.range (hiddenConstraintMap (q := q) K row).dualMap := by
  refine ⟨LinearMap.proj r, ?_⟩
  ext a
  rfl

/-- The span of hidden row forms is contained in the dual hidden-constraint
range. -/
theorem span_atomLinearForms_le_hidden_dualMap_range [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S) :
    Submodule.span K (Set.range fun r : ρ => atomLinearForm (q := q) K (row r)) ≤
      LinearMap.range (hiddenConstraintMap (q := q) K row).dualMap := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨r, rfl⟩
  exact atomLinearForm_mem_hidden_dualMap_range (q := q) (K := K) row r

/-- Row-span rank is bounded by the hidden constraint rank.  This is the only
linear-algebra bridge used by the connected-graph lower bound below; the
standard row/column-rank comparison is supplied by Mathlib via dual maps. -/
theorem finrank_span_atomLinearForms_le_hiddenRank [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S) :
    Module.finrank K
        (Submodule.span K (Set.range fun r : ρ => atomLinearForm (q := q) K (row r))) ≤
      hiddenRank (q := q) K row := by
  have hle :=
    Submodule.finrank_mono (span_atomLinearForms_le_hidden_dualMap_range (q := q) (K := K) row)
  have hdual :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (hiddenConstraintMap (q := q) K row)
  unfold hiddenRank
  exact hle.trans_eq hdual

/-- Atom-level adjacency, ignoring hidden/shifted color. -/
def atomLinked {S : Finset (Fin q)} (A : Finset (Atom S)) (i j : Fin q) : Prop :=
  ∃ atom ∈ A,
    (i = atom.edge.1.1 ∧ j = atom.edge.1.2) ∨
      (i = atom.edge.1.2 ∧ j = atom.edge.1.1)

/-- Reversing an edge negates its difference row. -/
theorem edgeDifferenceLinearForm_swap [Field K] (i j : Fin q) :
    edgeDifferenceLinearForm (q := q) K (j, i) =
      - edgeDifferenceLinearForm (q := q) K (i, j) := by
  ext a
  simp [edgeDifferenceLinearForm, sub_eq_add_neg, add_comm]

/-- Edge-difference rows telescope along paths. -/
theorem edgeDifferenceLinearForm_trans [Field K] (i j k : Fin q) :
    edgeDifferenceLinearForm (q := q) K (i, k) =
      edgeDifferenceLinearForm (q := q) K (i, j) +
        edgeDifferenceLinearForm (q := q) K (j, k) := by
  ext a
  simp [edgeDifferenceLinearForm, sub_eq_add_neg, add_left_comm, add_assoc]

/-- One atom-adjacency edge contributes its oriented edge-difference row to the
atom row span. -/
theorem edgeDifference_mem_span_atomLinearForms_of_atomLinked [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {i j : Fin q}
    (h : atomLinked A i j) :
    edgeDifferenceLinearForm (q := q) K (i, j) ∈
      Submodule.span K
        (Set.range fun atom : A => atomLinearForm (q := q) K (atomFamilyRow A atom)) := by
  rcases h with ⟨atom, hatom, hdir | hdir⟩
  · rcases hdir with ⟨rfl, rfl⟩
    exact Submodule.subset_span ⟨⟨atom, hatom⟩, rfl⟩
  · rcases hdir with ⟨rfl, rfl⟩
    have hmem : atomLinearForm (q := q) K atom ∈
        Submodule.span K
          (Set.range fun atom : A => atomLinearForm (q := q) K (atomFamilyRow A atom)) :=
      Submodule.subset_span ⟨⟨atom, hatom⟩, rfl⟩
    rw [atomLinearForm] at hmem
    rw [edgeDifferenceLinearForm_swap]
    exact Submodule.neg_mem _ hmem

/-- Every vertex reachable from a root has its root-difference row in the atom
row span. -/
theorem edgeDifference_mem_span_atomLinearForms_of_reachable [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {r i : Fin q}
    (h : Relation.ReflTransGen (atomLinked A) r i) :
    edgeDifferenceLinearForm (q := q) K (i, r) ∈
      Submodule.span K
        (Set.range fun atom : A => atomLinearForm (q := q) K (atomFamilyRow A atom)) := by
  induction h with
  | refl =>
      simp [edgeDifferenceLinearForm]
  | tail _ hxy ih =>
      rw [edgeDifferenceLinearForm_trans (K := K) _ _ _]
      exact Submodule.add_mem _
        (by
          rw [edgeDifferenceLinearForm_swap]
          exact Submodule.neg_mem _
            (edgeDifference_mem_span_atomLinearForms_of_atomLinked (q := q) (K := K) A hxy)) ih

/-- The root-difference rows for all non-root vertices in a finite set are
linearly independent. -/
theorem starEdgeDifference_linearIndependent [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) (r : Fin q) :
    LinearIndependent K
      (fun i : {i // i ∈ (atomVertices A).erase r} =>
        edgeDifferenceLinearForm (q := q) K (i.1, r)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  let x : Fin q → K := fun j => if j = i.1 then 1 else 0
  have happly := congrArg (fun f : (Fin q → K) →ₗ[K] K => f x) hsum
  have hir : i.1 ≠ r := by
    exact (Finset.mem_erase.mp i.2).1
  have hri : r ≠ i.1 := hir.symm
  simpa [x, edgeDifferenceLinearForm, hir, hri, Finset.sum_ite_eq'] using happly

/-- Connected atom families have hidden rank at least `|V|-1`, where `V` is
the set of touched vertices.  The connectivity hypothesis is stated as
reachability from a selected root in the atom adjacency relation. -/
theorem hiddenRank_atomFamilyRow_ge_card_sub_one_of_root_reaches [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {r : Fin q}
    (hr : r ∈ atomVertices A)
    (hreach : ∀ i ∈ atomVertices A, Relation.ReflTransGen (atomLinked A) r i) :
    (atomVertices A).card - 1 ≤
      hiddenRank (q := q) K (atomFamilyRow A) := by
  let Star := Submodule.span K
    (Set.range fun i : {i // i ∈ (atomVertices A).erase r} =>
      edgeDifferenceLinearForm (q := q) K (i.1, r))
  let Rows := Submodule.span K
    (Set.range fun atom : A => atomLinearForm (q := q) K (atomFamilyRow A atom))
  have hstar_le_rows : Star ≤ Rows := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨i, rfl⟩
    have hi_vertices : i.1 ∈ atomVertices A := (Finset.mem_erase.mp i.2).2
    exact edgeDifference_mem_span_atomLinearForms_of_reachable (q := q) (K := K) A
      (hreach i.1 hi_vertices)
  have hstar_rank : Module.finrank K Star = (atomVertices A).card - 1 := by
    have hli := starEdgeDifference_linearIndependent (q := q) (K := K) A r
    rw [show Star = Submodule.span K
      (Set.range fun i : {i // i ∈ (atomVertices A).erase r} =>
        edgeDifferenceLinearForm (q := q) K (i.1, r)) by rfl]
    rw [finrank_span_eq_card hli]
    rw [← Finset.card_erase_of_mem hr]
    exact Fintype.card_coe _
  have hstar_le_hidden :
      Module.finrank K Star ≤ hiddenRank (q := q) K (atomFamilyRow A) := by
    exact (Submodule.finrank_mono hstar_le_rows).trans
      (finrank_span_atomLinearForms_le_hiddenRank (q := q) (K := K) (atomFamilyRow A))
  rw [← hstar_rank]
  exact hstar_le_hidden

/-- Algebraic visible-defect predicate: the visible RHS map has a nonzero
obstruction modulo the hidden row space.  The later Penrose/cluster layer must
show that each surviving nonconstant cluster supplies this predicate. -/
def HasVisibleObstruction (K : Type*) [Field K] {ρ : Type*} [Fintype ρ]
    {S : Finset (Fin q)} (row : ρ → Atom S) : Prop :=
  ∃ y : Fin q → K, visibleObstructionMap (q := q) K row y ≠ 0

/-- Absence of a visible obstruction implies full hidden-fiber cardinality is
independent of the visible transcript.  This is the linear-algebraic core of
the remaining uncertified-term cancellation: non-obstructed raw terms should be
constant after the correct local/global fiber normalization. -/
theorem atomFamily_solution_card_eq_of_not_hasVisibleObstruction
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S))
    (hno : ¬ HasVisibleObstruction (q := q) K (atomFamilyRow A))
    (y y' : Fin q → K) :
    Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} =
      Fintype.card {a : Fin q → K // AtomFamilyHolds y' a A} := by
  apply atomFamily_solution_card_eq_of_forall_feasible (q := q) (K := K) A ?_ y y'
  intro z
  have hzero : visibleObstructionMap (q := q) K (atomFamilyRow A) z = 0 := by
    by_contra hz
    exact hno ⟨z, hz⟩
  rcases (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) (atomFamilyRow A) z).mpr hzero with ⟨a, ha⟩
  exact ⟨a, (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
    (K := K) z a A).mpr ha⟩

/-- Local version of `atomFamily_solution_card_eq_of_not_hasVisibleObstruction`.
The outside-support factor is independent of `y`, so it cancels from the full
fiber cardinality identity. -/
theorem card_atomFamilyHoldsOn_eq_of_not_hasVisibleObstruction
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S))
    (hno : ¬ HasVisibleObstruction (q := q) K (atomFamilyRow A))
    (y y' : Fin q → K) :
    Fintype.card {aS : S → K // AtomFamilyHoldsOn (q := q) y A aS} =
      Fintype.card {aS : S → K // AtomFamilyHoldsOn (q := q) y' A aS} := by
  have hfull := atomFamily_solution_card_eq_of_not_hasVisibleObstruction
    (q := q) (K := K) A hno y y'
  rw [card_atomFamily_hiddenFiber_eq_outside_mul_local (q := q) (G := K) A y] at hfull
  rw [card_atomFamily_hiddenFiber_eq_outside_mul_local (q := q) (G := K) A y'] at hfull
  exact Nat.mul_left_cancel (Fintype.card_pos (α := ({i : Fin q // i ∉ S} → K)))
    hfull

/-- Any local hidden-fiber count with no visible obstruction is killed by a
nonempty ANOVA component.  This is the general constant-fiber cancellation
interface for uncertified acyclic atom-choice terms. -/
theorem anovaComponent_atomChoiceFiber_eq_zero_of_not_hasVisibleObstruction
    [Field K] [Fintype K] [DecidableEq K]
    {S₀ : Finset (Fin q)} (A : Finset (Atom S₀))
    (hno : ¬ HasVisibleObstruction (q := q) K (atomFamilyRow A))
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    anovaComponent S
      (fun y : Fin q → K =>
        (Fintype.card {aS : S₀ → K //
          AtomFamilyHoldsOn (q := q) y A aS} : ℝ)) =
      fun _ => 0 := by
  apply Eq.trans ?_ (anovaComponent_const_of_nonempty (G := K) (q := q) hS
    ((Fintype.card {aS : S₀ → K //
      AtomFamilyHoldsOn (q := q) (Classical.arbitrary (Fin q → K)) A aS} : ℝ)))
  congr 1
  funext y
  exact_mod_cast card_atomFamilyHoldsOn_eq_of_not_hasVisibleObstruction
    (q := q) (K := K) A hno y (Classical.arbitrary (Fin q → K))

/-- A nonzero visible obstruction has visible rank at least one. -/
theorem visibleObstructionRank_pos_of_hasVisibleObstruction [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)} (row : ρ → Atom S)
    (h : HasVisibleObstruction (q := q) K row) :
    1 ≤ visibleObstructionRank (q := q) K row := by
  rcases h with ⟨y, hy⟩
  unfold visibleObstructionRank
  rw [Nat.succ_le_iff, Module.finrank_pos_iff]
  exact ⟨⟨visibleObstructionMap (q := q) K row y, ⟨y, rfl⟩⟩, 0, by
    intro hzero
    exact hy (congrArg Subtype.val hzero)⟩

theorem hasVisibleObstruction_atomFamily_mono [Field K] [DecidableEq K]
    {U S : Finset (Fin q)} (hUS : U ⊆ S) (A : Finset (Atom U))
    (hvis : HasVisibleObstruction (q := q) K (atomFamilyRow A)) :
    HasVisibleObstruction (q := q) K (atomFamilyRow (atomFamily_mono hUS A)) := by
  rcases hvis with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  intro hzero
  have hfeas := (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) (atomFamilyRow (atomFamily_mono hUS A)) y).mpr hzero
  rcases hfeas with ⟨a, ha⟩
  have hholds_global : AtomFamilyHolds y a (atomFamily_mono hUS A) :=
    (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
      (q := q) (K := K) y a (atomFamily_mono hUS A)).mpr ha
  have hholds_local : AtomFamilyHolds y a A :=
    (atomFamilyHolds_atomFamily_mono_iff (q := q) (G := K) hUS y a A).mp hholds_global
  have hfeas_local : ∃ a : Fin q → K,
      hiddenConstraintMap (q := q) K (atomFamilyRow A) a =
        visibleRhsMap (q := q) K (atomFamilyRow A) y :=
    ⟨a, (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
      (q := q) (K := K) y a A).mp hholds_local⟩
  have hzero_local := (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) (atomFamilyRow A) y).mp hfeas_local
  exact hy hzero_local

theorem hasVisibleObstruction_supportPartitionAtomFamily_of_block [Field K] [DecidableEq K]
    {S : Finset (Fin q)} (P : Finpartition S)
    (blockAtoms : (B : P.parts) → Finset (Atom B.1)) (B : P.parts)
    (hvis : HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms B))) :
    HasVisibleObstruction (q := q) K
      (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) := by
  rcases hvis with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  intro hzero
  have hfeas := (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) y).mpr hzero
  rcases hfeas with ⟨a, ha⟩
  have hholds_global : AtomFamilyHolds y a (supportPartitionAtomFamily P blockAtoms) :=
    (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
      (q := q) (K := K) y a (supportPartitionAtomFamily P blockAtoms)).mpr ha
  have hholds_block : AtomFamilyHolds y a (blockAtoms B) :=
    (atomFamilyHolds_supportPartitionAtomFamily_iff (q := q) (G := K)
      P blockAtoms y a).mp hholds_global B
  have hfeas_block : ∃ a : Fin q → K,
      hiddenConstraintMap (q := q) K (atomFamilyRow (blockAtoms B)) a =
        visibleRhsMap (q := q) K (atomFamilyRow (blockAtoms B)) y :=
    ⟨a, (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap
      (q := q) (K := K) y a (blockAtoms B)).mp hholds_block⟩
  have hzero_block := (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) (atomFamilyRow (blockAtoms B)) y).mp hfeas_block
  exact hy hzero_block

/-- Connected atom families with a visible obstruction have joint codimension
at least their number of touched vertices.  This is the algebraic codimension
form consumed by the cluster-activity estimate. -/
theorem jointRank_atomFamilyRow_ge_card_of_root_reaches_and_visibleObstruction [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {r : Fin q}
    (hr : r ∈ atomVertices A)
    (hreach : ∀ i ∈ atomVertices A, Relation.ReflTransGen (atomLinked A) r i)
    (hvis : HasVisibleObstruction (q := q) K (atomFamilyRow A)) :
    (atomVertices A).card ≤ jointRank (q := q) K (atomFamilyRow A) := by
  have hhidden :=
    hiddenRank_atomFamilyRow_ge_card_sub_one_of_root_reaches (q := q) (K := K) A hr hreach
  have hvisible :=
    visibleObstructionRank_pos_of_hasVisibleObstruction (q := q) (K := K)
      (atomFamilyRow A) hvis
  have hcard_pos : 0 < (atomVertices A).card := Finset.card_pos.mpr ⟨r, hr⟩
  have hsum : (atomVertices A).card ≤
      visibleObstructionRank (q := q) K (atomFamilyRow A) +
        hiddenRank (q := q) K (atomFamilyRow A) := by
    omega
  rw [visibleObstructionRank_add_hiddenRank_eq_jointRank] at hsum
  exact hsum

/-- Support-partition rank budget from per-block connected visible-defect
budgets, conditional on the still-missing block-diagonal rank-sum inequality.

This is the theorem-facing adapter for the support-partition route: the only
remaining algebraic leaf is to prove that the global lifted atom family has
joint rank at least the sum of the block-local joint ranks. -/
theorem jointRank_supportPartitionAtomFamily_ge_card_of_blocks_of_rank_sum [Field K]
    {S : Finset (Fin q)} (P : Finpartition S)
    (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hblocks : ∀ B : P.parts, atomVertices (blockAtoms B) = B.1)
    (hconn : ∀ B : P.parts, ∃ r,
      r ∈ atomVertices (blockAtoms B) ∧
      ∀ i ∈ atomVertices (blockAtoms B),
        Relation.ReflTransGen (atomLinked (blockAtoms B)) r i)
    (hvis : ∀ B : P.parts,
      HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms B)))
    (hrank_sum : (∑ B : P.parts,
      jointRank (q := q) K (atomFamilyRow (blockAtoms B))) ≤
        jointRank (q := q) K
          (atomFamilyRow (supportPartitionAtomFamily P blockAtoms))) :
    S.card ≤ jointRank (q := q) K
      (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) := by
  have hblock : ∀ B : P.parts,
      B.1.card ≤ jointRank (q := q) K (atomFamilyRow (blockAtoms B)) := by
    intro B
    rcases hconn B with ⟨r, hr, hreach⟩
    have h := jointRank_atomFamilyRow_ge_card_of_root_reaches_and_visibleObstruction
      (q := q) (K := K) (blockAtoms B) hr hreach (hvis B)
    simpa [hblocks B] using h
  have hsum_rank : (∑ B : P.parts, B.1.card) ≤
      ∑ B : P.parts, jointRank (q := q) K (atomFamilyRow (blockAtoms B)) := by
    exact Finset.sum_le_sum (fun B _ => hblock B)
  have hsum_card : (∑ B : P.parts, B.1.card) = S.card := by
    rw [← P.sum_card_parts]
    exact Finset.sum_attach P.parts (fun B => B.card)
  exact hsum_card ▸ hsum_rank.trans hrank_sum

theorem jointRank_supportPartitionAtomFamily_ge_card_of_blocks [Field K]
    {S : Finset (Fin q)} (P : Finpartition S)
    (blockAtoms : (B : P.parts) → Finset (Atom B.1))
    (hblocks : ∀ B : P.parts, atomVertices (blockAtoms B) = B.1)
    (hconn : ∀ B : P.parts, ∃ r,
      r ∈ atomVertices (blockAtoms B) ∧
      ∀ i ∈ atomVertices (blockAtoms B),
        Relation.ReflTransGen (atomLinked (blockAtoms B)) r i)
    (hvis : ∀ B : P.parts,
      HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms B))) :
    S.card ≤ jointRank (q := q) K
      (atomFamilyRow (supportPartitionAtomFamily P blockAtoms)) := by
  exact jointRank_supportPartitionAtomFamily_ge_card_of_blocks_of_rank_sum
    (q := q) (K := K) P blockAtoms hblocks hconn hvis
    (jointRank_supportPartitionAtomFamily_ge_sum (q := q) (K := K) P blockAtoms)

theorem jointRank_ge_card_of_supportPartitionClusterBlockAtoms [Field K]
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S)
    (A : Finset (Atom S))
    (blockAtoms : (B : i.1.parts) → Finset (Atom B.1))
    (hatoms : A = supportPartitionAtomFamily i.1 blockAtoms)
    (hblocks : ∀ B : i.1.parts, atomVertices (blockAtoms B) = B.1)
    (hconn : ∀ B : i.1.parts, ∃ r,
      r ∈ atomVertices (blockAtoms B) ∧
      ∀ j ∈ atomVertices (blockAtoms B),
        Relation.ReflTransGen (atomLinked (blockAtoms B)) r j)
    (hvis : ∀ B : i.1.parts,
      HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms B))) :
    S.card ≤ jointRank (q := q) K (atomFamilyRow A) := by
  subst hatoms
  exact jointRank_supportPartitionAtomFamily_ge_card_of_blocks (q := q) (K := K)
    i.1 blockAtoms hblocks hconn hvis

/-- Hidden-atom adjacency, using only hidden atoms from the selected family.
This is the formal mixed-cycle interface: a shifted atom whose endpoints are
connected by this relation creates a visible obstruction. -/
def hiddenAtomLinked {S : Finset (Fin q)} (A : Finset (Atom S)) (i j : Fin q) : Prop :=
  ∃ e : PairEdge S, hiddenAtom e ∈ A ∧
    ((i = e.1.1 ∧ j = e.1.2) ∨ (i = e.1.2 ∧ j = e.1.1))

/-- A hidden atom edge equates its two hidden endpoint variables. -/
theorem hiddenAtomLinked_eq_of_atomFamilyHolds [Field K]
    {S : Finset (Fin q)} {A : Finset (Atom S)} {i j : Fin q} {y a : Fin q → K}
    (hholds : AtomFamilyHolds y a A) (hlink : hiddenAtomLinked A i j) :
    a i = a j := by
  rcases hlink with ⟨e, he, hdir | hdir⟩
  · rcases hdir with ⟨rfl, rfl⟩
    have h := hholds (hiddenAtom e) he
    simpa [atomHolds_hidden, pairBadHidden] using h
  · rcases hdir with ⟨rfl, rfl⟩
    have h := hholds (hiddenAtom e) he
    have heq : a e.1.1 = a e.1.2 := by
      simpa [atomHolds_hidden, pairBadHidden] using h
    exact heq.symm

/-- Hidden-atom paths equate their endpoint hidden variables. -/
theorem hiddenAtomReachable_eq_of_atomFamilyHolds [Field K]
    {S : Finset (Fin q)} {A : Finset (Atom S)} {i j : Fin q} {y a : Fin q → K}
    (hholds : AtomFamilyHolds y a A)
    (hreach : Relation.ReflTransGen (hiddenAtomLinked A) i j) :
    a i = a j := by
  induction hreach with
  | refl => rfl
  | tail _ hxy ih =>
      exact ih.trans (hiddenAtomLinked_eq_of_atomFamilyHolds (K := K) hholds hxy)

/-- A shifted atom whose endpoints are already connected by hidden atoms is a
visible-defect witness: choosing a visible tuple with unequal endpoint values
makes the affine row system infeasible. -/
theorem hasVisibleObstruction_of_shiftedAtom_hiddenReachable [Field K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {e : PairEdge S}
    (hshift : shiftedAtom e ∈ A)
    (hreach : Relation.ReflTransGen (hiddenAtomLinked A) e.1.1 e.1.2) :
    HasVisibleObstruction (q := q) K (atomFamilyRow A) := by
  let y : Fin q → K := fun i => if i = e.1.2 then 1 else 0
  refine ⟨y, ?_⟩
  intro hzero
  have hfeas := (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) (atomFamilyRow A) y).mpr hzero
  rcases hfeas with ⟨a, ha⟩
  have hholds : AtomFamilyHolds y a A :=
    (atomFamilyHolds_iff_hiddenConstraintMap_eq_visibleRhsMap (K := K) y a A).mpr ha
  have hahidden : a e.1.1 = a e.1.2 :=
    hiddenAtomReachable_eq_of_atomFamilyHolds (K := K) hholds hreach
  have hshift_hold := hholds (shiftedAtom e) hshift
  have hraw : a e.1.1 + y e.1.1 = a e.1.2 + y e.1.2 := by
    simpa [atomHolds_shifted, pairBadShifted] using hshift_hold
  have hleft : y e.1.1 = 0 := by
    have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2.2.2
    simp [y, hne]
  have hright : y e.1.2 = 1 := by
    simp [y]
  rw [hleft, hright, hahidden] at hraw
  have hzeroone : (0 : K) = 1 := by
    exact add_left_cancel hraw
  exact zero_ne_one hzeroone

/-- General left-kernel visible-defect certificate.

This is the algebraic interface expected from a colored cycle or Penrose
survival proof: a nontrivial linear combination of hidden rows cancels, while
the same coefficients applied to the visible RHS are not identically zero. -/
theorem hasVisibleObstruction_of_leftKernel_rhs_ne [Field K]
    {ρ : Type*} [Fintype ρ] {S : Finset (Fin q)}
    (row : ρ → Atom S) (c : ρ → K)
    (hlin : (∑ r, c r • atomLinearForm (q := q) K (row r)) = 0)
    (hrhs : ∃ y : Fin q → K, (∑ r, c r * atomRhs y (row r)) ≠ 0) :
    HasVisibleObstruction (q := q) K row := by
  rcases hrhs with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  intro hzero
  have hfeas := (exists_hidden_solution_iff_visibleObstruction_eq_zero
    (q := q) (K := K) row y).mpr hzero
  rcases hfeas with ⟨a, ha⟩
  have happly := congrArg (fun f : (Fin q → K) →ₗ[K] K => f a) hlin
  have hsum_zero : (∑ r, c r * atomLinearForm (q := q) K (row r) a) = 0 := by
    simpa [LinearMap.sum_apply] using happly
  have hrow : ∀ r, atomLinearForm (q := q) K (row r) a = atomRhs y (row r) := by
    intro r
    simpa [hiddenConstraintMap_apply, visibleRhsMap_apply] using congrFun ha r
  have hsum_rhs : (∑ r, c r * atomRhs y (row r)) = 0 := by
    calc
      (∑ r, c r * atomRhs y (row r)) =
          ∑ r, c r * atomLinearForm (q := q) K (row r) a := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [hrow r]
      _ = 0 := hsum_zero
  exact hy hsum_rhs

/-- Exact joint-codimension mass plus a rank lower bound gives the corresponding
inverse-field-size probability bound. -/
theorem atomFamily_joint_card_density_le_inv_pow_of_jointRank_ge [Field K] [Fintype K]
    [DecidableEq K] {S : Finset (Fin q)} (A : Finset (Atom S)) {v : Nat}
    (hvr : v ≤ jointRank (q := q) K (atomFamilyRow A)) :
    ((Fintype.card { ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 A } : NNReal) /
      (Fintype.card ((Fin q → K) × (Fin q → K)) : NNReal)) ≤
      1 / (Fintype.card K : NNReal) ^ v := by
  rw [atomFamily_joint_card_density_eq_inv_pow (q := q) (K := K) A]
  rw [one_div, one_div]
  let b : NNReal := Fintype.card K
  have hbpos : 0 < b := by
    dsimp [b]
    exact_mod_cast (Fintype.card_pos (α := K))
  have hbone : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α := K)))
  have hpow : b ^ v ≤ b ^ jointRank (q := q) K (atomFamilyRow A) :=
    pow_le_pow_right' hbone hvr
  exact inv_anti₀ (pow_pos hbpos v) hpow

/-- Probability form of the connected visible-obstruction codimension bound. -/
theorem atomFamily_joint_card_density_le_inv_pow_card_of_root_reaches_and_visibleObstruction
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {r : Fin q}
    (hr : r ∈ atomVertices A)
    (hreach : ∀ i ∈ atomVertices A, Relation.ReflTransGen (atomLinked A) r i)
    (hvis : HasVisibleObstruction (q := q) K (atomFamilyRow A)) :
    ((Fintype.card { ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 A } : NNReal) /
      (Fintype.card ((Fin q → K) × (Fin q → K)) : NNReal)) ≤
      1 / (Fintype.card K : NNReal) ^ (atomVertices A).card := by
  exact atomFamily_joint_card_density_le_inv_pow_of_jointRank_ge (q := q) (K := K) A
    (jointRank_atomFamilyRow_ge_card_of_root_reaches_and_visibleObstruction
      (q := q) (K := K) A hr hreach hvis)

/-- The full hidden/shifted atomization of one pair edge.  This is a bridge
object for rank estimates after the pair-Mayer/Penrose layer has selected pair
edges; it is not a replacement for the pair-level expansion. -/
def pairEdgeFullAtoms {S : Finset (Fin q)} (e : PairEdge S) : Finset (Atom S) :=
  {hiddenAtom e, shiftedAtom e}

/-- Full hidden/shifted atomization of a finite pair-edge family. -/
def pairFamilyFullAtoms {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) : Finset (Atom S) :=
  Γ.biUnion pairEdgeFullAtoms

@[simp]
theorem hiddenAtom_mem_pairEdgeFullAtoms {S : Finset (Fin q)} (e : PairEdge S) :
    hiddenAtom e ∈ pairEdgeFullAtoms e := by
  simp [pairEdgeFullAtoms]

@[simp]
theorem shiftedAtom_mem_pairEdgeFullAtoms {S : Finset (Fin q)} (e : PairEdge S) :
    shiftedAtom e ∈ pairEdgeFullAtoms e := by
  simp [pairEdgeFullAtoms]

/-- A full pair-edge atom family holds exactly when both the hidden and shifted
collision equations for that pair edge hold. -/
theorem atomFamilyHolds_pairEdgeFullAtoms_iff [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (e : PairEdge S) (y a : Fin q → G) :
    AtomFamilyHolds y a (pairEdgeFullAtoms e) ↔
      pairBadHidden a e.1 ∧ pairBadShifted y a e.1 := by
  constructor
  · intro h
    exact ⟨by simpa using h (hiddenAtom e) (hiddenAtom_mem_pairEdgeFullAtoms e),
      by simpa using h (shiftedAtom e) (shiftedAtom_mem_pairEdgeFullAtoms e)⟩
  · rintro ⟨hh, hs⟩ atom hatom
    simp [pairEdgeFullAtoms] at hatom
    rcases hatom with rfl | rfl
    · simpa using hh
    · simpa using hs

/-- On a two-point support, the full hidden/shifted atom fiber over a pair edge
is the whole field when the visible endpoints agree. -/
noncomputable def pairEdgeFullAtomsCardTwoFiberEquiv
    [AddGroup K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2) (e : PairEdge S)
    (y : Fin q → K) (hy : y e.1.1 = y e.1.2) :
    {aS : S → K // AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} ≃ K where
  toFun aS := aS.1 ⟨e.1.1, e.2.1⟩
  invFun x := ⟨fun _ => x, by
    unfold AtomFamilyHoldsOn
    rw [atomFamilyHolds_pairEdgeFullAtoms_iff]
    constructor
    · unfold pairBadHidden
      rw [supportSubtypeLift_eq_of_mem (q := q) (fun _ : S => x) e.2.1,
        supportSubtypeLift_eq_of_mem (q := q) (fun _ : S => x) e.2.2.1]
    · unfold pairBadShifted
      rw [supportSubtypeLift_eq_of_mem (q := q) (fun _ : S => x) e.2.1,
        supportSubtypeLift_eq_of_mem (q := q) (fun _ : S => x) e.2.2.1]
      simp [hy]⟩
  left_inv := by
    intro aS
    apply Subtype.ext
    funext i
    have hcover : i.1 ∈ edgeVertices ({e} : Finset (PairEdge S)) := by
      rw [Mayer.edgeVertices_singleton_eq_support_of_card_eq_two (q := q) hcard e]
      exact i.2
    rw [edgeVertices] at hcover
    simp at hcover
    rcases hcover with hi | hi
    · have hiSubtype : i = ⟨e.1.1, e.2.1⟩ := Subtype.ext hi
      subst i
      rfl
    · have hiSubtype : i = ⟨e.1.2, e.2.2.1⟩ := Subtype.ext hi
      subst i
      have hh := (atomFamilyHolds_pairEdgeFullAtoms_iff (G := K) e y
        (supportSubtypeLift (q := q) aS.1)).mp aS.2 |>.1
      unfold pairBadHidden at hh
      rw [supportSubtypeLift_eq_of_mem (q := q) aS.1 e.2.1,
        supportSubtypeLift_eq_of_mem (q := q) aS.1 e.2.2.1] at hh
      simpa using hh
  right_inv := by
    intro x
    rfl

/-- Cardinality form of `pairEdgeFullAtomsCardTwoFiberEquiv`. -/
theorem card_pairEdgeFullAtoms_cardTwo_eq_of_visible_eq
    [AddGroup K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2) (e : PairEdge S)
    (y : Fin q → K) (hy : y e.1.1 = y e.1.2) :
    Fintype.card {aS : S → K // AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} =
      Fintype.card K := by
  exact Fintype.card_congr (pairEdgeFullAtomsCardTwoFiberEquiv (q := q) hcard e y hy)

/-- On a two-point support, the full hidden/shifted atom fiber over a pair edge
is empty when the visible endpoints differ. -/
theorem card_pairEdgeFullAtoms_cardTwo_eq_zero_of_visible_ne
    [AddGroup K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (e : PairEdge S)
    (y : Fin q → K) (hy : y e.1.1 ≠ y e.1.2) :
    Fintype.card {aS : S → K // AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} = 0 := by
  classical
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun aS => ?_⟩
  have hboth := (atomFamilyHolds_pairEdgeFullAtoms_iff (G := K) e y
    (supportSubtypeLift (q := q) aS.1)).mp aS.2
  unfold pairBadHidden pairBadShifted at hboth
  have hhidden : supportSubtypeLift (q := q) aS.1 e.1.1 =
      supportSubtypeLift (q := q) aS.1 e.1.2 := by
    simpa using hboth.1
  have hshift : supportSubtypeLift (q := q) aS.1 e.1.1 + y e.1.1 =
      supportSubtypeLift (q := q) aS.1 e.1.2 + y e.1.2 := by
    simpa using hboth.2
  rw [hhidden] at hshift
  exact hy (add_left_cancel hshift)

/-- Pointwise normal form for the two-point full hidden/shifted atom fiber. -/
theorem card_pairEdgeFullAtoms_cardTwo
    [AddGroup K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2) (e : PairEdge S)
    (y : Fin q → K) :
    Fintype.card {aS : S → K // AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} =
      if y e.1.1 = y e.1.2 then Fintype.card K else 0 := by
  by_cases hy : y e.1.1 = y e.1.2
  · simp [hy, card_pairEdgeFullAtoms_cardTwo_eq_of_visible_eq (q := q) hcard e y hy]
  · simp [hy, card_pairEdgeFullAtoms_cardTwo_eq_zero_of_visible_ne (q := q) e y hy]

/-- A full pair-edge-family atomization holds exactly when every selected pair
edge satisfies both its hidden and shifted collision equations. -/
theorem atomFamilyHolds_pairFamilyFullAtoms_iff [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y a : Fin q → G) :
    AtomFamilyHolds y a (pairFamilyFullAtoms Γ) ↔
      ∀ e ∈ Γ, pairBadHidden a e.1 ∧ pairBadShifted y a e.1 := by
  constructor
  · intro h e he
    have hhidden : hiddenAtom e ∈ pairFamilyFullAtoms Γ := by
      rw [pairFamilyFullAtoms]
      exact Finset.mem_biUnion.mpr ⟨e, he, hiddenAtom_mem_pairEdgeFullAtoms e⟩
    have hshifted : shiftedAtom e ∈ pairFamilyFullAtoms Γ := by
      rw [pairFamilyFullAtoms]
      exact Finset.mem_biUnion.mpr ⟨e, he, shiftedAtom_mem_pairEdgeFullAtoms e⟩
    exact ⟨by simpa using h (hiddenAtom e) hhidden,
      by simpa using h (shiftedAtom e) hshifted⟩
  · intro h atom hatom
    rw [pairFamilyFullAtoms] at hatom
    rcases Finset.mem_biUnion.mp hatom with ⟨e, he, hatomEdge⟩
    exact (atomFamilyHolds_pairEdgeFullAtoms_iff (G := G) e y a).mpr (h e he) atom hatomEdge

/-- Pair-Mayer factor rewritten by inclusion-exclusion over the two atom
constraints on one pair edge.  This is the atomization boundary required by the
rank route: the pair-level cancellation is kept intact until after the
pair-Mayer factor has been formed. -/
theorem pairMayerFactor_eq_atom_inclusion_exclusion [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (e : PairEdge S) (y a : Fin q → G) :
    pairMayerFactor y a e.1 =
      - (if atomHolds y a (hiddenAtom e) then (1 : ℝ) else 0)
      - (if atomHolds y a (shiftedAtom e) then (1 : ℝ) else 0)
      + (if AtomFamilyHolds y a (pairEdgeFullAtoms e) then (1 : ℝ) else 0) := by
  have hfull :
      AtomFamilyHolds y a (pairEdgeFullAtoms e) ↔
        pairBadHidden a e.1 ∧ pairBadShifted y a e.1 := by
    exact atomFamilyHolds_pairEdgeFullAtoms_iff (G := G) e y a
  by_cases hhidden : pairBadHidden a e.1
  · by_cases hshifted : pairBadShifted y a e.1
    · simp [pairMayerFactor, pairBad, pairBadHidden, pairBadShifted, atomHolds,
        hiddenAtom, shiftedAtom, hfull] at *
      simp [hhidden]
    · simp [pairMayerFactor, pairBad, pairBadHidden, pairBadShifted, atomHolds,
        hiddenAtom, shiftedAtom, hfull] at *
      simp [hhidden]
  · by_cases hshifted : pairBadShifted y a e.1
    · simp [pairMayerFactor, pairBad, pairBadHidden, pairBadShifted, atomHolds,
        hiddenAtom, shiftedAtom, hfull] at *
      simp [hhidden, hshifted]
    · simp [pairMayerFactor, pairBad, pairBadHidden, pairBadShifted, atomHolds,
        hiddenAtom, shiftedAtom, hfull] at *
      simp [hhidden, hshifted]

/-- Nonzero atom choices appearing in the inclusion-exclusion expansion of a
single pair-Mayer factor.  There is no empty choice because the pair-Mayer
factor itself is `-1_{hidden ∪ shifted}`, not `1 - 1_{...}`. -/
inductive PairAtomChoice where
  | hidden
  | shifted
  | both
deriving DecidableEq

instance pairAtomChoiceFintype : Fintype PairAtomChoice where
  elems := {PairAtomChoice.hidden, PairAtomChoice.shifted, PairAtomChoice.both}
  complete := by
    intro c
    cases c <;> simp

/-- Coefficient of one nonzero atom choice in the pair-Mayer
inclusion-exclusion expansion. -/
def pairAtomChoiceCoeff : PairAtomChoice → ℝ
  | PairAtomChoice.hidden => -1
  | PairAtomChoice.shifted => -1
  | PairAtomChoice.both => 1

/-- Atom family selected by one pair-atom choice. -/
def pairAtomChoiceAtoms {S : Finset (Fin q)} (e : PairEdge S) :
    PairAtomChoice → Finset (Atom S)
  | PairAtomChoice.hidden => {hiddenAtom e}
  | PairAtomChoice.shifted => {shiftedAtom e}
  | PairAtomChoice.both => pairEdgeFullAtoms e

@[simp]
theorem atomVertices_pairAtomChoiceAtoms {S : Finset (Fin q)}
    (e : PairEdge S) (choice : PairAtomChoice) :
    atomVertices (pairAtomChoiceAtoms e choice) = {e.1.1, e.1.2} := by
  cases choice <;> simp [pairAtomChoiceAtoms, pairEdgeFullAtoms, atomVertices,
    hiddenAtom, shiftedAtom]

theorem atom_mem_pairAtomChoiceAtoms_edge_eq {S : Finset (Fin q)}
    {e : PairEdge S} {choice : PairAtomChoice} {atom : Atom S}
    (hatom : atom ∈ pairAtomChoiceAtoms e choice) :
    atom.edge = e := by
  cases choice <;> simp [pairAtomChoiceAtoms, pairEdgeFullAtoms, hiddenAtom, shiftedAtom] at hatom
  · cases hatom
    rfl
  · cases hatom
    rfl
  · rcases hatom with hatom | hatom <;> cases hatom <;> rfl

theorem exists_atom_mem_pairAtomChoiceAtoms {S : Finset (Fin q)}
    (e : PairEdge S) (choice : PairAtomChoice) :
    ∃ atom ∈ pairAtomChoiceAtoms e choice, atom.edge = e := by
  cases choice
  · exact ⟨hiddenAtom e, by simp [pairAtomChoiceAtoms], rfl⟩
  · exact ⟨shiftedAtom e, by simp [pairAtomChoiceAtoms], rfl⟩
  · exact ⟨hiddenAtom e, by simp [pairAtomChoiceAtoms, pairEdgeFullAtoms], rfl⟩

theorem hiddenAtom_mem_pairAtomChoiceAtoms_of_choice {S : Finset (Fin q)}
    (e : PairEdge S) {choice : PairAtomChoice}
    (hchoice : choice = PairAtomChoice.hidden ∨ choice = PairAtomChoice.both) :
    hiddenAtom e ∈ pairAtomChoiceAtoms e choice := by
  rcases hchoice with rfl | rfl <;> simp [pairAtomChoiceAtoms, pairEdgeFullAtoms]

theorem shiftedAtom_mem_pairAtomChoiceAtoms_of_choice {S : Finset (Fin q)}
    (e : PairEdge S) {choice : PairAtomChoice}
    (hchoice : choice = PairAtomChoice.shifted ∨ choice = PairAtomChoice.both) :
    shiftedAtom e ∈ pairAtomChoiceAtoms e choice := by
  rcases hchoice with rfl | rfl <;> simp [pairAtomChoiceAtoms, pairEdgeFullAtoms]

/-- One-edge pair-Mayer factor as a finite sum over its three nonzero
inclusion-exclusion atom choices. -/
theorem pairMayerFactor_eq_sum_pairAtomChoices [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (e : PairEdge S) (y a : Fin q → G) :
    pairMayerFactor y a e.1 =
      ∑ choice : PairAtomChoice,
        pairAtomChoiceCoeff choice *
          (if AtomFamilyHolds y a (pairAtomChoiceAtoms e choice) then (1 : ℝ) else 0) := by
  rw [pairMayerFactor_eq_atom_inclusion_exclusion (G := G) (q := q) e y a]
  have hhidden_single :
      AtomFamilyHolds y a ({hiddenAtom e} : Finset (Atom S)) ↔ pairBadHidden a e.1 := by
    constructor
    · intro h
      simpa using h (hiddenAtom e) (by simp)
    · intro hh atom hatom
      simp at hatom
      subst hatom
      simpa using hh
  have hshifted_single :
      AtomFamilyHolds y a ({shiftedAtom e} : Finset (Atom S)) ↔ pairBadShifted y a e.1 := by
    constructor
    · intro h
      simpa using h (shiftedAtom e) (by simp)
    · intro hs atom hatom
      simp at hatom
      subst hatom
      simpa using hs
  have hboth :
      AtomFamilyHolds y a ({hiddenAtom e, shiftedAtom e} : Finset (Atom S)) ↔
        pairBadHidden a e.1 ∧ pairBadShifted y a e.1 := by
    constructor
    · intro h
      exact ⟨by simpa using h (hiddenAtom e) (by simp),
        by simpa using h (shiftedAtom e) (by simp)⟩
    · rintro ⟨hh, hs⟩ atom hatom
      simp at hatom
      rcases hatom with rfl | rfl
      · simpa using hh
      · simpa using hs
  have huniv :
      (Finset.univ : Finset PairAtomChoice) =
        {PairAtomChoice.hidden, PairAtomChoice.shifted, PairAtomChoice.both} := by
    ext choice
    cases choice <;> simp
  rw [show (∑ choice : PairAtomChoice,
      pairAtomChoiceCoeff choice *
        (if AtomFamilyHolds y a (pairAtomChoiceAtoms e choice) then (1 : ℝ) else 0)) =
      ∑ choice ∈ ({PairAtomChoice.hidden, PairAtomChoice.shifted, PairAtomChoice.both} :
          Finset PairAtomChoice),
        pairAtomChoiceCoeff choice *
          (if AtomFamilyHolds y a (pairAtomChoiceAtoms e choice) then (1 : ℝ) else 0) by
        rw [← huniv]]
  simp [pairAtomChoiceCoeff, pairAtomChoiceAtoms, pairEdgeFullAtoms,
    hhidden_single, hshifted_single, hboth]
  by_cases hhidden : pairBadHidden a e.1 <;>
    by_cases hshifted : pairBadShifted y a e.1 <;>
      simp [hhidden, hshifted]

/-- Product of pair-Mayer factors expanded into independent atom choices on
each selected pair edge.  This is still a pair-level expansion: the choices are
made only after each pair-Mayer factor has already performed its local
inclusion-exclusion. -/
theorem pairMayerProduct_eq_sum_pairAtomChoiceFamilies [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y a : Fin q → G) :
    (∏ e ∈ Γ, pairMayerFactor y a e.1) =
      ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        ∏ e : {e // e ∈ Γ},
          pairAtomChoiceCoeff (choice e) *
            (if AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 (choice e)) then (1 : ℝ) else 0) := by
  classical
  calc
    (∏ e ∈ Γ, pairMayerFactor y a e.1) =
        ∏ e : {e // e ∈ Γ}, pairMayerFactor y a e.1.1 := by
          exact (Finset.prod_attach Γ (fun e => pairMayerFactor y a e.1)).symm
    _ =
        ∏ e : {e // e ∈ Γ},
          ∑ choice : PairAtomChoice,
            pairAtomChoiceCoeff choice *
              (if AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 choice) then (1 : ℝ) else 0) := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          exact pairMayerFactor_eq_sum_pairAtomChoices (G := G) (q := q) e.1 y a
    _ =
      ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        ∏ e : {e // e ∈ Γ},
          pairAtomChoiceCoeff (choice e) *
            (if AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 (choice e)) then (1 : ℝ) else 0) := by
      exact Fintype.prod_sum
        (fun (e : {e // e ∈ Γ}) (choice : PairAtomChoice) =>
          pairAtomChoiceCoeff choice *
            (if AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 choice) then (1 : ℝ) else 0))

/-- Atom family selected by independent atom choices on every edge of a
pair-edge family. -/
def pairAtomChoiceFamilyAtoms {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) : Finset (Atom S) :=
  (Finset.univ : Finset {e // e ∈ Γ}).biUnion
    (fun e => pairAtomChoiceAtoms e.1 (choice e))

/-- Atom choices over a singleton pair-edge family reduce to the chosen atom
set on that one edge. -/
theorem pairAtomChoiceFamilyAtoms_singleton {S : Finset (Fin q)} (e : PairEdge S)
    (choice : (e' : {e' // e' ∈ ({e} : Finset (PairEdge S))}) → PairAtomChoice) :
    pairAtomChoiceFamilyAtoms ({e} : Finset (PairEdge S)) choice =
      pairAtomChoiceAtoms e (choice ⟨e, by simp⟩) := by
  classical
  unfold pairAtomChoiceFamilyAtoms
  ext atom
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e', hatom⟩
    have heqval : (e' : PairEdge S) = e := Finset.mem_singleton.mp e'.2
    have heq : e' = ⟨e, by simp⟩ := by
      apply Subtype.ext
      exact heqval
    simpa [heq] using hatom
  · intro hatom
    exact ⟨⟨e, by simp⟩, hatom⟩

/-- A single hidden atom has no visible obstruction: the zero hidden assignment
solves it for every visible transcript. -/
theorem not_hasVisibleObstruction_pairAtomChoiceAtoms_hidden
    [Field K] {S : Finset (Fin q)} (e : PairEdge S) :
    ¬ HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceAtoms e PairAtomChoice.hidden)) := by
  intro h
  rcases h with ⟨y, hy⟩
  have hzero : visibleObstructionMap (q := q) K
      (atomFamilyRow (pairAtomChoiceAtoms e PairAtomChoice.hidden)) y = 0 := by
    apply (exists_hidden_solution_iff_visibleObstruction_eq_zero
      (q := q) (K := K)
      (atomFamilyRow (pairAtomChoiceAtoms e PairAtomChoice.hidden)) y).mp
    refine ⟨fun _ => 0, ?_⟩
    funext r
    have hr : (r : Atom S) = hiddenAtom e := by
      have hmem : (r : Atom S) ∈ ({hiddenAtom e} : Finset (Atom S)) := by
        rw [show ({hiddenAtom e} : Finset (Atom S)) =
          pairAtomChoiceAtoms e PairAtomChoice.hidden by rfl]
        exact r.2
      exact Finset.mem_singleton.mp hmem
    cases r with
    | mk atom _hmem =>
        simp only at hr
        subst atom
        simp [hiddenConstraintMap_apply, visibleRhsMap_apply, atomFamilyRow,
          atomLinearForm, atomRhs, edgeDifferenceLinearForm, hiddenAtom]
  exact hy hzero

/-- A single shifted atom has no visible obstruction: one can always choose a
hidden assignment satisfying the shifted edge equation. -/
theorem not_hasVisibleObstruction_pairAtomChoiceAtoms_shifted
    [Field K] {S : Finset (Fin q)} (e : PairEdge S) :
    ¬ HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceAtoms e PairAtomChoice.shifted)) := by
  intro h
  rcases h with ⟨y, hy⟩
  let a : Fin q → K := fun i =>
    if i = e.1.1 then y e.1.2 - y e.1.1 else 0
  have hzero : visibleObstructionMap (q := q) K
      (atomFamilyRow (pairAtomChoiceAtoms e PairAtomChoice.shifted)) y = 0 := by
    apply (exists_hidden_solution_iff_visibleObstruction_eq_zero
      (q := q) (K := K)
      (atomFamilyRow (pairAtomChoiceAtoms e PairAtomChoice.shifted)) y).mp
    refine ⟨a, ?_⟩
    funext r
    have hr : (r : Atom S) = shiftedAtom e := by
      have hmem : (r : Atom S) ∈ ({shiftedAtom e} : Finset (Atom S)) := by
        rw [show ({shiftedAtom e} : Finset (Atom S)) =
          pairAtomChoiceAtoms e PairAtomChoice.shifted by rfl]
        exact r.2
      exact Finset.mem_singleton.mp hmem
    cases r with
    | mk atom _hmem =>
        simp only at hr
        subst atom
        have hne : e.1.2 ≠ e.1.1 := (ne_of_lt e.2.2.2).symm
        simp [hiddenConstraintMap_apply, visibleRhsMap_apply, atomFamilyRow,
          atomLinearForm, atomRhs, edgeDifferenceLinearForm, shiftedAtom, a, hne]
  exact hy hzero

@[simp]
theorem atomVertices_pairAtomChoiceFamilyAtoms {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) :
    atomVertices (pairAtomChoiceFamilyAtoms Γ choice) = edgeVertices Γ := by
  ext i
  constructor
  · intro hi
    rw [atomVertices] at hi
    rw [edgeVertices]
    rw [Finset.mem_biUnion] at hi ⊢
    rcases hi with ⟨atom, hatomFamily, hiAtom⟩
    rw [pairAtomChoiceFamilyAtoms, Finset.mem_biUnion] at hatomFamily
    rcases hatomFamily with ⟨e, _heUniv, hatomChoice⟩
    refine ⟨e.1, e.2, ?_⟩
    have hedge := atom_mem_pairAtomChoiceAtoms_edge_eq hatomChoice
    simpa [hedge] using hiAtom
  · intro hi
    rw [edgeVertices, Finset.mem_biUnion] at hi
    rw [atomVertices, Finset.mem_biUnion]
    rcases hi with ⟨e, heΓ, hiEdge⟩
    rcases exists_atom_mem_pairAtomChoiceAtoms e (choice ⟨e, heΓ⟩) with
      ⟨atom, hatomChoice, hedge⟩
    refine ⟨atom, ?_, ?_⟩
    · rw [pairAtomChoiceFamilyAtoms, Finset.mem_biUnion]
      exact ⟨⟨e, heΓ⟩, Finset.mem_univ _, hatomChoice⟩
    · simpa [hedge] using hiEdge

theorem atomLinked_pairAtomChoiceFamilyAtoms_of_edgeLinked {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    {i j : Fin q} (hlink : edgeLinked Γ i j) :
    atomLinked (pairAtomChoiceFamilyAtoms Γ choice) i j := by
  rcases hlink with ⟨e, heΓ, hdir⟩
  rcases exists_atom_mem_pairAtomChoiceAtoms e (choice ⟨e, heΓ⟩) with
    ⟨atom, hatomChoice, hedge⟩
  refine ⟨atom, ?_, ?_⟩
  · rw [pairAtomChoiceFamilyAtoms, Finset.mem_biUnion]
    exact ⟨⟨e, heΓ⟩, Finset.mem_univ _, hatomChoice⟩
  · simpa [hedge] using hdir

theorem atomLinked_reflTransGen_pairAtomChoiceFamilyAtoms_of_edgeLinked_reflTransGen
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) {i j : Fin q}
    (hreach : Relation.ReflTransGen (edgeLinked Γ) i j) :
    Relation.ReflTransGen (atomLinked (pairAtomChoiceFamilyAtoms Γ choice)) i j := by
  induction hreach with
  | refl => rfl
  | tail _ htail ih =>
      exact Relation.ReflTransGen.tail ih
        (atomLinked_pairAtomChoiceFamilyAtoms_of_edgeLinked Γ choice htail)

theorem pairAtomChoiceFamily_root_reaches_of_pairConnected {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hconn : PairConnected Γ) {r : Fin q} (hr : r ∈ edgeVertices Γ) :
    ∀ i ∈ atomVertices (pairAtomChoiceFamilyAtoms Γ choice),
      Relation.ReflTransGen (atomLinked (pairAtomChoiceFamilyAtoms Γ choice)) r i := by
  intro i hi
  have hiEdge : i ∈ edgeVertices Γ := by
    simpa [atomVertices_pairAtomChoiceFamilyAtoms Γ choice] using hi
  exact atomLinked_reflTransGen_pairAtomChoiceFamilyAtoms_of_edgeLinked_reflTransGen
    Γ choice (hconn r hr i hiEdge)

theorem hiddenRank_pairAtomChoiceFamily_ge_card_sub_one_of_pairConnected [Field K]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hconn : PairConnected Γ) {r : Fin q} (hr : r ∈ edgeVertices Γ) :
    (edgeVertices Γ).card - 1 ≤
      hiddenRank (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice)) := by
  have hrAtom : r ∈ atomVertices (pairAtomChoiceFamilyAtoms Γ choice) := by
    simpa [atomVertices_pairAtomChoiceFamilyAtoms Γ choice] using hr
  have hreach := pairAtomChoiceFamily_root_reaches_of_pairConnected Γ choice hconn hr
  have hrank :=
    hiddenRank_atomFamilyRow_ge_card_sub_one_of_root_reaches
      (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice) hrAtom hreach
  simpa [atomVertices_pairAtomChoiceFamilyAtoms Γ choice] using hrank

theorem hiddenRank_pairFamilyComponentAtomChoice_ge_card_sub_one [Field K]
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent)
    (choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice) :
    (pairFamilyComponentVertices Γ C).card - 1 ≤
      hiddenRank (q := q) K
        (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice)) := by
  rcases pairFamilyComponentVertices_nonempty Γ C with ⟨r, hr⟩
  have hrEdge : r ∈ edgeVertices (pairFamilyComponentEdgeFamily Γ C) := by
    rwa [edgeVertices_pairFamilyComponentEdgeFamily]
  have hrank :=
    hiddenRank_pairAtomChoiceFamily_ge_card_sub_one_of_pairConnected
      (q := q) (K := K) (pairFamilyComponentEdgeFamily Γ C) choice
      (pairFamilyComponentEdgeFamily_pairConnected Γ C) hrEdge
  simpa [edgeVertices_pairFamilyComponentEdgeFamily] using hrank

theorem jointRank_pairAtomChoiceFamily_ge_card_of_pairConnected_and_visibleObstruction
    [Field K] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hconn : PairConnected Γ) {r : Fin q} (hr : r ∈ edgeVertices Γ)
    (hvis : HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))) :
    (edgeVertices Γ).card ≤
      jointRank (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice)) := by
  have hrAtom : r ∈ atomVertices (pairAtomChoiceFamilyAtoms Γ choice) := by
    simpa [atomVertices_pairAtomChoiceFamilyAtoms Γ choice] using hr
  have hreach := pairAtomChoiceFamily_root_reaches_of_pairConnected Γ choice hconn hr
  have hrank :=
    jointRank_atomFamilyRow_ge_card_of_root_reaches_and_visibleObstruction
      (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice) hrAtom hreach hvis
  simpa [atomVertices_pairAtomChoiceFamilyAtoms Γ choice] using hrank

theorem jointRank_pairFamilyComponentAtomChoice_ge_card_of_visibleObstruction [Field K]
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent)
    (choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice)
    (hvis : HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice))) :
    (pairFamilyComponentVertices Γ C).card ≤
      jointRank (q := q) K
        (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice)) := by
  rcases pairFamilyComponentVertices_nonempty Γ C with ⟨r, hr⟩
  have hrEdge : r ∈ edgeVertices (pairFamilyComponentEdgeFamily Γ C) := by
    rwa [edgeVertices_pairFamilyComponentEdgeFamily]
  have hrank :=
    jointRank_pairAtomChoiceFamily_ge_card_of_pairConnected_and_visibleObstruction
      (q := q) (K := K) (pairFamilyComponentEdgeFamily Γ C) choice
      (pairFamilyComponentEdgeFamily_pairConnected Γ C) hrEdge hvis
  simpa [edgeVertices_pairFamilyComponentEdgeFamily] using hrank

theorem shiftedAtom_mem_pairAtomChoiceFamilyAtoms_of_choice {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    {e : PairEdge S} (he : e ∈ Γ)
    (hchoice : choice ⟨e, he⟩ = PairAtomChoice.shifted ∨
      choice ⟨e, he⟩ = PairAtomChoice.both) :
    shiftedAtom e ∈ pairAtomChoiceFamilyAtoms Γ choice := by
  rw [pairAtomChoiceFamilyAtoms, Finset.mem_biUnion]
  exact ⟨⟨e, he⟩, Finset.mem_univ _,
    shiftedAtom_mem_pairAtomChoiceAtoms_of_choice e hchoice⟩

theorem hiddenAtom_mem_pairAtomChoiceFamilyAtoms_of_choice {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    {e : PairEdge S} (he : e ∈ Γ)
    (hchoice : choice ⟨e, he⟩ = PairAtomChoice.hidden ∨
      choice ⟨e, he⟩ = PairAtomChoice.both) :
    hiddenAtom e ∈ pairAtomChoiceFamilyAtoms Γ choice := by
  rw [pairAtomChoiceFamilyAtoms, Finset.mem_biUnion]
  exact ⟨⟨e, he⟩, Finset.mem_univ _,
    hiddenAtom_mem_pairAtomChoiceAtoms_of_choice e hchoice⟩

theorem hasVisibleObstruction_of_pairAtomChoiceFamily_shifted_hiddenReachable [Field K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    {e : PairEdge S} (he : e ∈ Γ)
    (hchoice : choice ⟨e, he⟩ = PairAtomChoice.shifted ∨
      choice ⟨e, he⟩ = PairAtomChoice.both)
    (hreach : Relation.ReflTransGen
      (hiddenAtomLinked (pairAtomChoiceFamilyAtoms Γ choice)) e.1.1 e.1.2) :
    HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice)) := by
  exact hasVisibleObstruction_of_shiftedAtom_hiddenReachable
    (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice)
    (shiftedAtom_mem_pairAtomChoiceFamilyAtoms_of_choice choice he hchoice) hreach

/-- A `both` choice contains its own hidden atom, hence its endpoints are
hidden-linked inside the selected atom family. -/
theorem hiddenAtomLinked_pairAtomChoiceFamilyAtoms_self_of_both {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    {e : PairEdge S} (he : e ∈ Γ)
    (hchoice : choice ⟨e, he⟩ = PairAtomChoice.both) :
    hiddenAtomLinked (pairAtomChoiceFamilyAtoms Γ choice) e.1.1 e.1.2 := by
  exact ⟨e, hiddenAtom_mem_pairAtomChoiceFamilyAtoms_of_choice choice he
    (Or.inr hchoice), Or.inl ⟨rfl, rfl⟩⟩

/-- Any atom-choice family containing a `both` edge is already
rank-certified: the shifted atom on that edge closes against its own hidden
atom. -/
theorem hasVisibleObstruction_of_pairAtomChoiceFamily_both [Field K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    {e : PairEdge S} (he : e ∈ Γ)
    (hchoice : choice ⟨e, he⟩ = PairAtomChoice.both) :
    HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice)) := by
  exact hasVisibleObstruction_of_pairAtomChoiceFamily_shifted_hiddenReachable
    (q := q) (K := K) choice he (Or.inr hchoice)
    (Relation.ReflTransGen.single
      (hiddenAtomLinked_pairAtomChoiceFamilyAtoms_self_of_both
        (q := q) choice he hchoice))

/-- Coefficient of an independent atom-choice family. -/
def pairAtomChoiceFamilyCoeff {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) : ℝ :=
  ∏ e : {e // e ∈ Γ}, pairAtomChoiceCoeff (choice e)

@[simp]
theorem abs_pairAtomChoiceCoeff (choice : PairAtomChoice) :
    |pairAtomChoiceCoeff choice| = (1 : ℝ) := by
  cases choice <;> norm_num [pairAtomChoiceCoeff]

@[simp]
theorem abs_pairAtomChoiceFamilyCoeff {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) :
    |pairAtomChoiceFamilyCoeff choice| = (1 : ℝ) := by
  simp [pairAtomChoiceFamilyCoeff, Finset.abs_prod]

/-- Holding the union of atom choices is equivalent to holding each edge's
selected atom family. -/
theorem atomFamilyHolds_pairAtomChoiceFamilyAtoms_iff [AddGroup G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) (y a : Fin q → G) :
    AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice) ↔
      ∀ e : {e // e ∈ Γ}, AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 (choice e)) := by
  constructor
  · intro h e atom hatom
    exact h atom (by
      unfold pairAtomChoiceFamilyAtoms
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hatom⟩)
  · intro h atom hatom
    unfold pairAtomChoiceFamilyAtoms at hatom
    rw [Finset.mem_biUnion] at hatom
    rcases hatom with ⟨e, _he, hatom⟩
    exact h e atom hatom

/-- The product of per-edge atom-family indicators is the indicator that the
union atom family holds. -/
theorem prod_pairAtomChoice_indicator_eq_family_indicator [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) (y a : Fin q → G) :
    (∏ e : {e // e ∈ Γ},
      (if AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 (choice e)) then (1 : ℝ) else 0)) =
        if AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice) then (1 : ℝ) else 0 := by
  classical
  by_cases hfamily : AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)
  · have hedge :
        ∀ e : {e // e ∈ Γ}, AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 (choice e)) :=
      (atomFamilyHolds_pairAtomChoiceFamilyAtoms_iff (G := G) Γ choice y a).mp hfamily
    simp [hfamily, hedge]
  · have hnot :
        ¬ ∀ e : {e // e ∈ Γ}, AtomFamilyHolds y a (pairAtomChoiceAtoms e.1 (choice e)) := by
      intro h
      exact hfamily ((atomFamilyHolds_pairAtomChoiceFamilyAtoms_iff (G := G) Γ choice y a).mpr h)
    rcases not_forall.mp hnot with ⟨e, he⟩
    rw [if_neg hfamily]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- Edge-family pair-Mayer product as a sum over selected atom families, with
one indicator per whole selected family. -/
theorem pairMayerProduct_eq_sum_pairAtomChoiceFamilyAtoms [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y a : Fin q → G) :
    (∏ e ∈ Γ, pairMayerFactor y a e.1) =
      ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        pairAtomChoiceFamilyCoeff choice *
          (if AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice) then (1 : ℝ) else 0) := by
  rw [pairMayerProduct_eq_sum_pairAtomChoiceFamilies (G := G) (q := q) Γ y a]
  refine Finset.sum_congr rfl ?_
  intro choice _hchoice
  unfold pairAtomChoiceFamilyCoeff
  rw [Finset.prod_mul_distrib]
  rw [prod_pairAtomChoice_indicator_eq_family_indicator (G := G) (q := q) Γ choice y a]

/-- Summing an atom-family indicator over hidden tuples counts the hidden
solutions of that selected atom family. -/
theorem sum_atomFamilyHolds_indicator_eq_card [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (A : Finset (Atom S)) (y : Fin q → G) :
    (∑ a : Fin q → G, if AtomFamilyHolds y a A then (1 : ℝ) else 0) =
      (Fintype.card {a : Fin q → G // AtomFamilyHolds y a A} : ℝ) := by
  classical
  let p := fun a : Fin q → G => AtomFamilyHolds y a A
  calc
    (∑ a : Fin q → G, if AtomFamilyHolds y a A then (1 : ℝ) else 0)
        = ((Finset.univ.filter p).card : ℝ) := by
          simp [p]
    _ = (Fintype.card {a : Fin q → G // AtomFamilyHolds y a A} : ℝ) := by
          exact_mod_cast (Fintype.card_subtype p).symm

/-- Pair-family hidden sum as an atom-choice expansion whose inner quantities
are hidden-solution fiber cardinalities. -/
theorem pairFamilyTerm_eq_sum_atomChoiceFamily_counts [AddGroup G] [Fintype G]
    [DecidableEq G] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → G) :
    pairFamilyTerm (G := G) Γ y =
      ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        pairAtomChoiceFamilyCoeff choice *
          (Fintype.card {a : Fin q → G //
            AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ) := by
  classical
  unfold pairFamilyTerm
  calc
    (∑ a : Fin q → G, ∏ e ∈ Γ, pairMayerFactor y a e.1) =
        ∑ a : Fin q → G,
          ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
            pairAtomChoiceFamilyCoeff choice *
              (if AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact pairMayerProduct_eq_sum_pairAtomChoiceFamilyAtoms (G := G) (q := q) Γ y a
    _ =
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          ∑ a : Fin q → G,
            pairAtomChoiceFamilyCoeff choice *
              (if AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice) then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ =
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          pairAtomChoiceFamilyCoeff choice *
            ∑ a : Fin q → G,
              (if AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro choice _hchoice
          rw [Finset.mul_sum]
    _ =
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          pairAtomChoiceFamilyCoeff choice *
            (Fintype.card {a : Fin q → G //
              AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro choice _hchoice
          rw [sum_atomFamilyHolds_indicator_eq_card (G := G) (q := q)
            (pairAtomChoiceFamilyAtoms Γ choice) y]

/-- Source-faithful signed block contribution: a connected pair cluster is
evaluated by the pair-Mayer product on a hidden assignment local to the cluster
support.  This keeps the signed `-hidden - shifted + both` pair-level
inclusion-exclusion, unlike the rejected positive full-atomized candidate. -/
def signedPairMayerBlockContribution [AddGroup G] [Fintype G] [DecidableEq G]
    (S : Finset (Fin q)) (C : PairCluster S) (y : Fin q → G) : ℝ :=
  ∑ aS : S → G,
    ∏ e ∈ Mayer.pairClusterSupportEdges C,
      pairMayerFactor y (supportSubtypeLift (q := q) aS) e.1

/-- The source-faithful signed block contribution expands into signed
atom-choice local hidden fibers.  This is the concrete block-local evaluation
needed by the corrected Penrose/Ursell branch. -/
theorem signedPairMayerBlockContribution_blockLocalEval
    [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → G) :
    signedPairMayerBlockContribution (G := G) (q := q) S C y =
      ∑ choice : (e : {e // e ∈ Mayer.pairClusterSupportEdges C}) → PairAtomChoice,
        pairAtomChoiceFamilyCoeff choice *
          (Fintype.card {aS : S → G //
            AtomFamilyHoldsOn (q := q) y
              (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice) aS} : ℝ) := by
  classical
  unfold signedPairMayerBlockContribution
  calc
    (∑ aS : S → G,
        ∏ e ∈ Mayer.pairClusterSupportEdges C,
          pairMayerFactor y (supportSubtypeLift (q := q) aS) e.1) =
        ∑ aS : S → G,
          ∑ choice : (e : {e // e ∈ Mayer.pairClusterSupportEdges C}) → PairAtomChoice,
            pairAtomChoiceFamilyCoeff choice *
              (if AtomFamilyHolds y (supportSubtypeLift (q := q) aS)
                  (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice)
                then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro aS _haS
          exact pairMayerProduct_eq_sum_pairAtomChoiceFamilyAtoms
            (G := G) (q := q) (Mayer.pairClusterSupportEdges C) y
            (supportSubtypeLift (q := q) aS)
    _ =
        ∑ choice : (e : {e // e ∈ Mayer.pairClusterSupportEdges C}) → PairAtomChoice,
          ∑ aS : S → G,
            pairAtomChoiceFamilyCoeff choice *
              (if AtomFamilyHolds y (supportSubtypeLift (q := q) aS)
                  (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice)
                then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ =
        ∑ choice : (e : {e // e ∈ Mayer.pairClusterSupportEdges C}) → PairAtomChoice,
          pairAtomChoiceFamilyCoeff choice *
            ∑ aS : S → G,
              (if AtomFamilyHolds y (supportSubtypeLift (q := q) aS)
                  (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice)
                then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro choice _hchoice
          rw [Finset.mul_sum]
    _ =
        ∑ choice : (e : {e // e ∈ Mayer.pairClusterSupportEdges C}) → PairAtomChoice,
          pairAtomChoiceFamilyCoeff choice *
            (Fintype.card {aS : S → G //
              AtomFamilyHoldsOn (q := q) y
                (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice) aS} : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro choice _hchoice
          rw [show (∑ aS : S → G,
              (if AtomFamilyHolds y (supportSubtypeLift (q := q) aS)
                  (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice)
                then (1 : ℝ) else 0)) =
              (∑ aS : S → G,
                if AtomFamilyHoldsOn (q := q) y
                    (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice) aS
                  then (1 : ℝ) else 0) by rfl]
          rw [sum_atomFamilyHoldsOn_indicator_eq_card]

/-- Predicate for the atom-choice family that selected only hidden-collision
atoms.  These terms carry no visible constraint and are killed by nonempty
ANOVA centering. -/
def PairAtomChoiceFamilyAllHidden {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) : Prop :=
  ∀ e, choice e = PairAtomChoice.hidden

/-- Hidden-only atom-choice families are independent of the visible transcript. -/
theorem atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_iff
    [AddGroup G] [DecidableEq G] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hhidden : PairAtomChoiceFamilyAllHidden (q := q) choice)
    (y : Fin q → G) (aS : S → G) :
    AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS ↔
      ∀ e : {e // e ∈ Γ}, pairBadHidden (supportSubtypeLift (q := q) aS) e.1.1 := by
  unfold AtomFamilyHoldsOn
  rw [atomFamilyHolds_pairAtomChoiceFamilyAtoms_iff]
  constructor
  · intro h e
    have he := h e
    rw [hhidden e] at he
    simpa [pairAtomChoiceAtoms, atomHolds, hiddenAtom, pairBadHidden] using
      he (hiddenAtom e.1) (by simp [pairAtomChoiceAtoms])
  · intro h e
    rw [hhidden e]
    intro atom hatom
    simp [pairAtomChoiceAtoms] at hatom
    subst hatom
    simpa [atomHolds, hiddenAtom, pairBadHidden] using h e

/-- The local hidden-fiber count of a hidden-only atom-choice family is constant
as the visible transcript varies. -/
theorem card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_eq
    [AddGroup G] [Fintype G] [DecidableEq G] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hhidden : PairAtomChoiceFamilyAllHidden (q := q) choice)
    (y y' : Fin q → G) :
    (Fintype.card {aS : S → G //
      AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ) =
    (Fintype.card {aS : S → G //
      AtomFamilyHoldsOn (q := q) y' (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ) := by
  have hiff : ∀ aS : S → G,
      AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS ↔
        AtomFamilyHoldsOn (q := q) y' (pairAtomChoiceFamilyAtoms Γ choice) aS := by
    intro aS
    rw [atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_iff
      (q := q) Γ choice hhidden y aS]
    rw [atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_iff
      (q := q) Γ choice hhidden y' aS]
  exact_mod_cast Fintype.card_congr (Equiv.subtypeEquivRight hiff)

/-- Hidden-only atom-choice fiber counts vanish after taking any nonempty ANOVA
component.  This is the first concrete low-rank cancellation leaf for the
corrected signed/certified route. -/
theorem anovaComponent_hiddenOnly_atomChoiceFiber_eq_zero_of_nonempty
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S₀ : Finset (Fin q)} (Γ : Finset (PairEdge S₀))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hhidden : PairAtomChoiceFamilyAllHidden (q := q) choice)
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    anovaComponent S
      (fun y : Fin q → G =>
        (Fintype.card {aS : S₀ → G //
          AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)) =
      fun _ => 0 := by
  apply Eq.trans ?_ (anovaComponent_const_of_nonempty (G := G) (q := q) hS
    ((Fintype.card {aS : S₀ → G //
      AtomFamilyHoldsOn (q := q) (Classical.arbitrary (Fin q → G))
        (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)))
  congr 1
  funext y
  exact card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_eq
    (q := q) Γ choice hhidden y (Classical.arbitrary (Fin q → G))

/-- Predicate for atom-choice families that selected only shifted-collision
atoms.  These terms also have constant hidden-fiber cardinality: translating
the local hidden assignment by the visible transcript converts shifted
constraints for one transcript into shifted constraints for any other. -/
def PairAtomChoiceFamilyAllShifted {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice) : Prop :=
  ∀ e, choice e = PairAtomChoice.shifted

/-- Visible-dependent translation between local hidden assignments. -/
noncomputable def shiftedLocalAssignmentEquiv [AddCommGroup G]
    {S : Finset (Fin q)} (y y' : Fin q → G) : (S → G) ≃ (S → G) where
  toFun := fun aS i => aS i + y i.1 - y' i.1
  invFun := fun aS i => aS i + y' i.1 - y i.1
  left_inv := by
    intro aS
    funext i
    simp
  right_inv := by
    intro aS
    funext i
    simp

/-- Shifted-only atom-choice families are equivalent to edgewise shifted
collision equations. -/
theorem atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_iff
    [AddGroup G] [DecidableEq G] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hshifted : PairAtomChoiceFamilyAllShifted (q := q) choice)
    (y : Fin q → G) (aS : S → G) :
    AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS ↔
      ∀ e : {e // e ∈ Γ}, pairBadShifted y (supportSubtypeLift (q := q) aS) e.1.1 := by
  unfold AtomFamilyHoldsOn
  rw [atomFamilyHolds_pairAtomChoiceFamilyAtoms_iff]
  constructor
  · intro h e
    have he := h e
    rw [hshifted e] at he
    simpa [pairAtomChoiceAtoms, atomHolds, shiftedAtom, pairBadShifted] using
      he (shiftedAtom e.1) (by simp [pairAtomChoiceAtoms])
  · intro h e
    rw [hshifted e]
    intro atom hatom
    simp [pairAtomChoiceAtoms] at hatom
    subst hatom
    simpa [atomHolds, shiftedAtom, pairBadShifted] using h e

/-- Translating local hidden assignments by `y - y'` transports shifted
constraints for transcript `y` to shifted constraints for transcript `y'`. -/
theorem pairBadShifted_shiftedLocalAssignmentEquiv
    [AddCommGroup G] {S : Finset (Fin q)} (y y' : Fin q → G)
    (aS : S → G) (e : PairEdge S) :
    pairBadShifted y'
        (supportSubtypeLift (q := q) ((shiftedLocalAssignmentEquiv (q := q) y y') aS))
        e.1 ↔
      pairBadShifted y (supportSubtypeLift (q := q) aS) e.1 := by
  unfold pairBadShifted
  have h1 : e.1.1 ∈ S := e.2.1
  have h2 : e.1.2 ∈ S := e.2.2.1
  simp [supportSubtypeLift, h1, h2, shiftedLocalAssignmentEquiv, add_comm]

/-- The local hidden-fiber count of a shifted-only atom-choice family is
constant as the visible transcript varies. -/
theorem card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_eq
    [AddCommGroup G] [Fintype G] [DecidableEq G] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hshifted : PairAtomChoiceFamilyAllShifted (q := q) choice)
    (y y' : Fin q → G) :
    (Fintype.card {aS : S → G //
      AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ) =
    (Fintype.card {aS : S → G //
      AtomFamilyHoldsOn (q := q) y' (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ) := by
  let e : (S → G) ≃ (S → G) := shiftedLocalAssignmentEquiv (q := q) y y'
  have hiff : ∀ aS : S → G,
      AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS ↔
        AtomFamilyHoldsOn (q := q) y' (pairAtomChoiceFamilyAtoms Γ choice) (e aS) := by
    intro aS
    rw [atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_iff
      (q := q) Γ choice hshifted y aS]
    rw [atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_iff
      (q := q) Γ choice hshifted y' (e aS)]
    constructor
    · intro h edge
      exact (pairBadShifted_shiftedLocalAssignmentEquiv (q := q) y y' aS edge.1).2
        (h edge)
    · intro h edge
      exact (pairBadShifted_shiftedLocalAssignmentEquiv (q := q) y y' aS edge.1).1
        (h edge)
  exact_mod_cast Fintype.card_congr (e.subtypeEquiv hiff)

/-- Shifted-only atom-choice fiber counts vanish after taking any nonempty
ANOVA component. -/
theorem anovaComponent_shiftedOnly_atomChoiceFiber_eq_zero_of_nonempty
    [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {S₀ : Finset (Fin q)} (Γ : Finset (PairEdge S₀))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hshifted : PairAtomChoiceFamilyAllShifted (q := q) choice)
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    anovaComponent S
      (fun y : Fin q → G =>
        (Fintype.card {aS : S₀ → G //
          AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)) =
      fun _ => 0 := by
  apply Eq.trans ?_ (anovaComponent_const_of_nonempty (G := G) (q := q) hS
    ((Fintype.card {aS : S₀ → G //
      AtomFamilyHoldsOn (q := q) (Classical.arbitrary (Fin q → G))
        (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)))
  congr 1
  funext y
  exact card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_eq
    (q := q) Γ choice hshifted y (Classical.arbitrary (Fin q → G))

/-- Raw atom-choice specialization of the general no-visible-obstruction
constant local-fiber theorem. -/
theorem card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_eq_of_not_hasVisibleObstruction
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hno : ¬ HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice)))
    (y y' : Fin q → K) :
    (Fintype.card {aS : S → K //
      AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ) =
    (Fintype.card {aS : S → K //
      AtomFamilyHoldsOn (q := q) y' (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ) := by
  exact_mod_cast card_atomFamilyHoldsOn_eq_of_not_hasVisibleObstruction
    (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice) hno y y'

/-- Raw atom-choice terms with no visible obstruction are killed by every
nonempty ANOVA component.  The certified resummation branch can therefore route
obstructed terms to the rank endpoint and non-obstructed terms to this
centering lemma. -/
theorem anovaComponent_atomChoiceFiber_eq_zero_of_not_hasVisibleObstruction'
    [Field K] [Fintype K] [DecidableEq K]
    {S₀ : Finset (Fin q)} (Γ : Finset (PairEdge S₀))
    (choice : (e : {e // e ∈ Γ}) → PairAtomChoice)
    (hno : ¬ HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice)))
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    anovaComponent S
      (fun y : Fin q → K =>
        (Fintype.card {aS : S₀ → K //
          AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)) =
      fun _ => 0 := by
  exact anovaComponent_atomChoiceFiber_eq_zero_of_not_hasVisibleObstruction
    (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice) hno hS

/-- Uniform hidden-fiber cardinality bound for a selected atom family.  This is
the feasible/infeasible wrapper needed by the atom-choice expansion: feasible
visible transcripts use the exact affine-fiber cardinality, and infeasible
transcripts contribute zero. -/
theorem atomFamily_solution_card_le_pow_hiddenRank [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) (y : Fin q → K) :
    Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} ≤
      Fintype.card K ^ (q - hiddenRank (q := q) K (atomFamilyRow A)) := by
  by_cases hfeas : ∃ a : Fin q → K, AtomFamilyHolds y a A
  · rw [atomFamily_solution_card_eq_pow_of_feasible (q := q) (K := K) A y hfeas]
  · have hEmpty : IsEmpty {a : Fin q → K // AtomFamilyHolds y a A} :=
      ⟨fun a => hfeas ⟨a.1, a.2⟩⟩
    have hcard : Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} = 0 :=
      Fintype.card_eq_zero
    rw [hcard]
    exact Nat.zero_le _

/-- Real-valued version of `atomFamily_solution_card_le_pow_hiddenRank`, ready for
triangle-inequality estimates on atom-choice expansions. -/
theorem atomFamily_solution_card_real_le_pow_hiddenRank [Field K] [Fintype K]
    [DecidableEq K] {S : Finset (Fin q)} (A : Finset (Atom S)) (y : Fin q → K) :
    (Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} : ℝ) ≤
      (Fintype.card K : ℝ) ^ (q - hiddenRank (q := q) K (atomFamilyRow A)) := by
  exact_mod_cast atomFamily_solution_card_le_pow_hiddenRank (q := q) (K := K) A y

/-- Summing hidden-fiber cardinalities over visible transcripts is the same as
counting joint hidden/visible solutions.  This is the finite Fubini step needed
before applying joint-rank codimension bounds. -/
theorem sum_atomFamily_solution_card_eq_joint_card [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) :
    (∑ y : Fin q → K, Fintype.card {a : Fin q → K // AtomFamilyHolds y a A}) =
      Fintype.card {ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 A} := by
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun ya => ⟨(ya.2.1, ya.1), ya.2.2⟩
      invFun := fun ay => ⟨ay.1.2, ⟨ay.1.1, ay.2⟩⟩
      left_inv := by
        intro ya
        cases ya with
        | mk y a =>
            cases a
            rfl
      right_inv := by
        intro ay
        cases ay with
        | mk ay h =>
            cases ay
            rfl }

/-- Visible average of selected atom-family hidden fibers, rewritten as a joint
solution count divided by the number of visible transcripts. -/
theorem uniformAverage_atomFamily_solution_card_eq_joint_card_div
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) :
    uniformAverage (Fin q → K)
        (fun y => (Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} : ℝ)) =
      (Fintype.card {ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 A} : ℝ) /
        (Fintype.card (Fin q → K) : ℝ) := by
  unfold uniformAverage
  rw [← Nat.cast_sum]
  rw [sum_atomFamily_solution_card_eq_joint_card (q := q) (K := K) A]

/-- Joint-rank lower bounds turn the exact joint solution count into an inverse
codimension cardinality bound. -/
theorem atomFamily_joint_card_le_pow_two_mul_sub_of_jointRank_ge
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {v : Nat}
    (hvr : v ≤ jointRank (q := q) K (atomFamilyRow A)) :
    Fintype.card {ay : (Fin q → K) × (Fin q → K) //
      AtomFamilyHolds ay.2 ay.1 A} ≤ Fintype.card K ^ (2 * q - v) := by
  rw [atomFamily_joint_card_eq_pow (q := q) (K := K) A]
  have hr_le : jointRank (q := q) K (atomFamilyRow A) ≤ 2 * q :=
    jointRank_le_two_mul_q (q := q) (K := K) A
  have hsub : 2 * q - jointRank (q := q) K (atomFamilyRow A) ≤ 2 * q - v := by
    omega
  exact Nat.pow_le_pow_right (Fintype.card_pos (α := K)) hsub

/-- Visible average of selected atom-family hidden fibers bounded by a joint-rank
codimension estimate.  This is the averaged version that recovers the visible
defect factor missing from pointwise hidden-rank bounds. -/
theorem uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (A : Finset (Atom S)) {v : Nat}
    (hvr : v ≤ jointRank (q := q) K (atomFamilyRow A)) :
    uniformAverage (Fin q → K)
        (fun y => (Fintype.card {a : Fin q → K // AtomFamilyHolds y a A} : ℝ)) ≤
      (Fintype.card K : ℝ) ^ (2 * q - v) / (Fintype.card K : ℝ) ^ q := by
  rw [uniformAverage_atomFamily_solution_card_eq_joint_card_div (q := q) (K := K) A]
  rw [Fintype.card_fun, Fintype.card_fin]
  rw [Nat.cast_pow]
  change
    (Fintype.card {ay : (Fin q → K) × (Fin q → K) //
      AtomFamilyHolds ay.2 ay.1 A} : ℝ) / (Fintype.card K : ℝ) ^ q ≤
      (Fintype.card K : ℝ) ^ (2 * q - v) / (Fintype.card K : ℝ) ^ q
  exact div_le_div_of_nonneg_right
    (by
      exact_mod_cast
        atomFamily_joint_card_le_pow_two_mul_sub_of_jointRank_ge
          (q := q) (K := K) A hvr)
    (by positivity)

/-- For nonnegative atom-family fiber counts, the visible `L¹` norm is just the
uniform visible average. -/
theorem visibleL1_atomFamily_solution_card_eq_uniformAverage
    [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (A : Finset (Atom S)) :
    visibleL1 (G := G) (q := q)
        (fun y => (Fintype.card {a : Fin q → G // AtomFamilyHolds y a A} : ℝ)) =
      uniformAverage (Fin q → G)
        (fun y => (Fintype.card {a : Fin q → G // AtomFamilyHolds y a A} : ℝ)) := by
  unfold visibleL1
  simp

/-- `L¹` bound for one pair-family hidden sum after pair-level atom-choice
expansion and joint-rank averaging.  The function `rankBudget` is the theorem
leaf that a Penrose or component argument must supply for each selected
atom-choice family. -/
theorem visibleL1_pairFamilyTerm_le_sum_atomChoiceFamily_jointRankBudget
    [Field K] [Fintype K] [DecidableEq K] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S))
    (rankBudget : ((e : {e // e ∈ Γ}) → PairAtomChoice) → Nat)
    (hvr : ∀ choice,
      rankBudget choice ≤ jointRank (q := q) K
        (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))) :
    visibleL1 (G := K) (q := q) (fun y => pairFamilyTerm (G := K) Γ y) ≤
      ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        (Fintype.card K : ℝ) ^ (2 * q - rankBudget choice) /
          (Fintype.card K : ℝ) ^ q := by
  have hterm :
      (fun y => pairFamilyTerm (G := K) Γ y) =
        fun y =>
          ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
            pairAtomChoiceFamilyCoeff choice *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ) := by
    funext y
    exact pairFamilyTerm_eq_sum_atomChoiceFamily_counts (G := K) (q := q) Γ y
  rw [hterm]
  calc
    visibleL1 (G := K) (q := q)
        (fun y =>
          ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
            pairAtomChoiceFamilyCoeff choice *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ)) ≤
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          visibleL1 (G := K) (q := q)
            (fun y =>
              pairAtomChoiceFamilyCoeff choice *
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ)) := by
          simpa using
            visibleL1_sum_le (G := K) (q := q)
              (Finset.univ : Finset ((e : {e // e ∈ Γ}) → PairAtomChoice))
              (fun choice y =>
                pairAtomChoiceFamilyCoeff choice *
                  (Fintype.card {a : Fin q → K //
                    AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ))
    _ =
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          visibleL1 (G := K) (q := q)
            (fun y =>
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro choice _hchoice
          rw [visibleL1_const_mul]
          simp
    _ ≤ ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        (Fintype.card K : ℝ) ^ (2 * q - rankBudget choice) /
          (Fintype.card K : ℝ) ^ q := by
          refine Finset.sum_le_sum ?_
          intro choice _hchoice
          rw [visibleL1_atomFamily_solution_card_eq_uniformAverage (G := K) (q := q)]
          exact uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge
            (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice) (hvr choice)

/-- Normalized pair-family `L¹` bound with the XoP visible normalizer left
explicit.  This is the atom-choice/rank budget interface consumed by the
covering-edge and component-factorized theorem spines. -/
theorem visibleL1_normalizedPairFamilyTerm_le_invNormalizer_mul_sum_atomChoiceFamily_jointRankBudget
    [Field K] [Fintype K] [DecidableEq K] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S))
    (rankBudget : ((e : {e // e ∈ Γ}) → PairAtomChoice) → Nat)
    (hvr : ∀ choice,
      rankBudget choice ≤ jointRank (q := q) K
        (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))) :
    visibleL1 (G := K) (q := q) (normalizedPairFamilyTerm (G := K) Γ) ≤
      |((visibleNormalizerNNReal (G := K) (q := q) : NNReal) : ℝ)⁻¹| *
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          (Fintype.card K : ℝ) ^ (2 * q - rankBudget choice) /
            (Fintype.card K : ℝ) ^ q := by
  have hnorm :
      normalizedPairFamilyTerm (G := K) Γ =
        fun y => (((visibleNormalizerNNReal (G := K) (q := q) : NNReal) : ℝ)⁻¹) *
          pairFamilyTerm (G := K) Γ y := by
    funext y
    simp [normalizedPairFamilyTerm, div_eq_mul_inv, mul_comm]
  rw [hnorm, visibleL1_const_mul]
  exact mul_le_mul_of_nonneg_left
      (visibleL1_pairFamilyTerm_le_sum_atomChoiceFamily_jointRankBudget
        (q := q) (K := K) Γ rankBudget hvr)
    (abs_nonneg _)

/-- Component-local hidden sums inherit atom-choice joint-rank budgets from the
full pair-family term of that component's edge family. -/
theorem visibleL1_pairFamilyComponentLocalSum_le_invComplement_mul_sum_atomChoiceFamily_jointRankBudget
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent)
    (rankBudget :
      ((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice) → Nat)
    (hvr : ∀ choice,
      rankBudget choice ≤ jointRank (q := q) K
        (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice))) :
    visibleL1 (G := K) (q := q) (pairFamilyComponentLocalSum (G := K) Γ C) ≤
      |((Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → K) : ℝ)⁻¹)| *
        ∑ choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice,
          (Fintype.card K : ℝ) ^ (2 * q - rankBudget choice) /
            (Fintype.card K : ℝ) ^ q := by
  let m : ℝ :=
    (Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → K) : ℝ)
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → K) ≠ 0)
  have hlocal :
      pairFamilyComponentLocalSum (G := K) Γ C =
        fun y => m⁻¹ * pairFamilyTerm (G := K) (pairFamilyComponentEdgeFamily Γ C) y := by
    funext y
    have hcomponent :=
      pairFamilyTerm_componentEdgeFamily_eq_complementCard_mul_localSum (G := K) Γ C y
    dsimp [m] at hcomponent ⊢
    calc
      pairFamilyComponentLocalSum (G := K) Γ C y =
          m⁻¹ * (m * pairFamilyComponentLocalSum (G := K) Γ C y) := by
            field_simp [hm_ne]
      _ = m⁻¹ * pairFamilyTerm (G := K) (pairFamilyComponentEdgeFamily Γ C) y := by
            rw [← hcomponent]
  rw [hlocal, visibleL1_const_mul]
  exact mul_le_mul_of_nonneg_left
      (visibleL1_pairFamilyTerm_le_sum_atomChoiceFamily_jointRankBudget
        (q := q) (K := K) (pairFamilyComponentEdgeFamily Γ C) rankBudget hvr)
    (abs_nonneg _)

/-- The component-local atomized rank budget exposed by the rank/codimension
bridge.  It is deliberately just the right-hand side of
`visibleL1_pairFamilyComponentLocalSum_le_invComplement_mul_sum_atomChoiceFamily_jointRankBudget`,
so downstream theorem statements can name the budget instead of repeating the
dependent atom-choice expression. -/
def componentLocalAtomizedRankBudget [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent)
    (rankBudget :
      ((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice) → Nat) : ℝ :=
  |((Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → K) : ℝ)⁻¹)| *
    ∑ choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice,
      (Fintype.card K : ℝ) ^ (2 * q - rankBudget choice) /
        (Fintype.card K : ℝ) ^ q

theorem componentLocalAtomizedRankBudget_nonneg [Field K] [Fintype K] [DecidableEq K]
    [Nonempty K] (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent)
    (rankBudget :
      ((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice) → Nat) :
    0 ≤ componentLocalAtomizedRankBudget (q := q) (K := K) Γ C rankBudget := by
  unfold componentLocalAtomizedRankBudget
  refine mul_nonneg (abs_nonneg _) ?_
  refine Finset.sum_nonneg ?_
  intro choice _hchoice
  exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)

theorem componentLocalAtomizedRankBudget_const_rank [Field K] [Fintype K]
    [DecidableEq K] [Nonempty K] (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) (v : Nat) :
    componentLocalAtomizedRankBudget (q := q) (K := K) Γ C (fun _choice => v) =
      |((Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → K) : ℝ)⁻¹)| *
        ((Fintype.card
          (((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice)) : ℝ) *
          ((Fintype.card K : ℝ) ^ (2 * q - v) / (Fintype.card K : ℝ) ^ q)) := by
  simp [componentLocalAtomizedRankBudget, Finset.sum_const, nsmul_eq_mul]

/-- Raw pair-atom choice families have exactly three choices per selected pair
edge.  This is the support-local version used by the certified scalar budget. -/
theorem card_pairAtomChoiceFamily {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) :
    Fintype.card (((e : {e // e ∈ Γ}) → PairAtomChoice)) = 3 ^ Γ.card := by
  rw [Fintype.card_fun]
  have hchoice : Fintype.card PairAtomChoice = 3 := by
    native_decide
  simp [Fintype.card_coe, hchoice]

theorem card_component_pairAtomChoiceFamily
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    Fintype.card (((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice)) =
      3 ^ (pairFamilyComponentEdgeFamily Γ C).card := by
  rw [card_pairAtomChoiceFamily]

theorem card_complement_function_space [Fintype K] (U : Finset (Fin q)) :
    Fintype.card ({ i : Fin q // i ∉ U } → K) =
      Fintype.card K ^ (q - U.card) := by
  classical
  rw [Fintype.card_fun]
  have hcompl :
      Fintype.card { i : Fin q // i ∉ U } = q - U.card := by
    have h := Fintype.card_subtype_compl (fun i : Fin q => i ∈ U)
    simp [Fintype.card_fin, Fintype.card_coe] at h ⊢
  rw [hcompl]

theorem componentLocalAtomizedRankBudget_visibleObstruction_eq_three_pow
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent) :
    componentLocalAtomizedRankBudget (q := q) (K := K) Γ C
      (fun _choice => (pairFamilyComponentVertices Γ C).card) =
      (3 : ℝ) ^ (pairFamilyComponentEdgeFamily Γ C).card := by
  rw [componentLocalAtomizedRankBudget_const_rank (q := q) (K := K) Γ C
    (pairFamilyComponentVertices Γ C).card]
  rw [card_component_pairAtomChoiceFamily (q := q) Γ C]
  rw [card_complement_function_space (q := q) (K := K) (pairFamilyComponentVertices Γ C)]
  let N : ℝ := Fintype.card K
  let v : Nat := (pairFamilyComponentVertices Γ C).card
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := K)
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hv_le : v ≤ q := by
    dsimp [v]
    have hsubset :
        pairFamilyComponentVertices Γ C ⊆ coordinates q :=
      (pairFamilyComponentVertices_subset_edgeVertices Γ C).trans (edgeVertices_subset Γ)
    simpa [coordinates] using Finset.card_le_card hsubset
  have hsub : 2 * q - v = q + (q - v) := by omega
  have hcard_pos : 0 < (Fintype.card K : ℝ) ^ (q - v) := by positivity
  rw [hsub]
  rw [pow_add]
  have hcancel :
      |(((Fintype.card K : ℝ) ^ (q - v) : ℝ)⁻¹)| *
          ((3 : ℝ) ^ (pairFamilyComponentEdgeFamily Γ C).card *
            (((Fintype.card K : ℝ) ^ q * (Fintype.card K : ℝ) ^ (q - v)) /
              (Fintype.card K : ℝ) ^ q)) =
        (3 : ℝ) ^ (pairFamilyComponentEdgeFamily Γ C).card := by
    rw [abs_of_pos (inv_pos.mpr hcard_pos)]
    field_simp [hN_ne, hN_pos.ne', N]
  simpa [N, v, mul_assoc] using hcancel

/-- Named component-local `L¹` estimate using `componentLocalAtomizedRankBudget`. -/
theorem visibleL1_pairFamilyComponentLocalSum_le_componentLocalAtomizedRankBudget
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (Γ : Finset (PairEdge (coordinates q)))
    (C : (pairFamilySupportGraph Γ).ConnectedComponent)
    (rankBudget :
      ((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice) → Nat)
    (hvr : ∀ choice,
      rankBudget choice ≤ jointRank (q := q) K
        (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice))) :
    visibleL1 (G := K) (q := q) (pairFamilyComponentLocalSum (G := K) Γ C) ≤
      componentLocalAtomizedRankBudget (q := q) (K := K) Γ C rankBudget := by
  exact visibleL1_pairFamilyComponentLocalSum_le_invComplement_mul_sum_atomChoiceFamily_jointRankBudget
    (q := q) (K := K) Γ C rankBudget hvr

/-- Component-local rank budgets feed the existing covering-route XoP endpoint.
The remaining leaves are now explicit: joint-rank lower bounds for every
component atom-choice family, a product-to-term-budget comparison, and the
covering-family summability estimate. -/
theorem xop_advantageOn_injective_of_componentLocalAtomizedRankBudget_geTwo_pow_small_q
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (ε : NNReal) {activity : Nat → ℝ} {a : ℝ}
    {termBudget : Finset (PairEdge (coordinates q)) → ℝ}
    (rankBudget :
      (Γ : Finset (PairEdge (coordinates q))) →
        (C : (pairFamilySupportGraph Γ).ConnectedComponent) →
          (((e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice) → Nat))
    (hq : q ≤ Fintype.card K)
    (hvr : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      ∀ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∀ choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice,
          rankBudget Γ C choice ≤ jointRank (q := q) K
            (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice)))
    (hterm : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → K) : ℝ) /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)| *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          componentLocalAtomizedRankBudget (q := q) (K := K) Γ C (rankBudget Γ C) ≤
          termBudget Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        (S.powerset.card : ℝ) * termBudget Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  refine Mayer.xop_advantageOn_injective_of_componentLocalL1Budget_geTwo_pow_small_q
    (G := K) (q := q) ε hq ?_ hterm hbudget ha hsmall hactivity hε
  intro Γ hΓ C
  exact visibleL1_pairFamilyComponentLocalSum_le_componentLocalAtomizedRankBudget
    (q := q) (K := K) Γ C (rankBudget Γ C) (hvr Γ hΓ C)

/-- Component-local endpoint with the rank budget fixed to the component vertex
count.  The remaining rank-side hypothesis is exactly the source-specific
visible-obstruction/survival condition for every atom-choice term. -/
theorem xop_advantageOn_injective_of_componentLocalVisibleObstructionBudget_geTwo_pow_small_q
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (ε : NNReal) {activity : Nat → ℝ} {a : ℝ}
    {termBudget : Finset (PairEdge (coordinates q)) → ℝ}
    (hq : q ≤ Fintype.card K)
    (hvis : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      ∀ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∀ choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice,
          HasVisibleObstruction (q := q) K
            (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice)))
    (hterm : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → K) : ℝ) /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)| *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          componentLocalAtomizedRankBudget (q := q) (K := K) Γ C
            (fun _choice => (pairFamilyComponentVertices Γ C).card) ≤
          termBudget Γ)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        (S.powerset.card : ℝ) * termBudget Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_componentLocalAtomizedRankBudget_geTwo_pow_small_q
    (K := K) (q := q) ε
    (rankBudget := fun Γ C _choice => (pairFamilyComponentVertices Γ C).card)
    hq ?_ hterm hbudget ha hsmall hactivity hε
  intro Γ hΓ C choice
  exact jointRank_pairFamilyComponentAtomChoice_ge_card_of_visibleObstruction
    (q := q) (K := K) Γ C choice (hvis Γ hΓ C choice)

/-- Concrete term budget obtained by multiplying the visible-obstruction
component rank budgets over the connected components of a pair-edge family. -/
def componentVisibleObstructionTermBudget [Field K] [Fintype K] [DecidableEq K]
    [Nonempty K] (Γ : Finset (PairEdge (coordinates q))) : ℝ :=
  |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → K) : ℝ) /
      (visibleNormalizerNNReal (G := K) (q := q) : ℝ)| *
    ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
      componentLocalAtomizedRankBudget (q := q) (K := K) Γ C
        (fun _choice => (pairFamilyComponentVertices Γ C).card)

theorem componentVisibleObstructionTermBudget_nonneg [Field K] [Fintype K]
    [DecidableEq K] [Nonempty K] (Γ : Finset (PairEdge (coordinates q))) :
    0 ≤ componentVisibleObstructionTermBudget (q := q) (K := K) Γ := by
  unfold componentVisibleObstructionTermBudget
  refine mul_nonneg (abs_nonneg _) ?_
  refine Finset.prod_nonneg ?_
  intro C _hC
  exact componentLocalAtomizedRankBudget_nonneg (q := q) (K := K) Γ C
    (fun _choice => (pairFamilyComponentVertices Γ C).card)

theorem componentVisibleObstructionTermBudget_eq_explicit [Field K] [Fintype K]
    [DecidableEq K] [Nonempty K] (Γ : Finset (PairEdge (coordinates q))) :
    componentVisibleObstructionTermBudget (q := q) (K := K) Γ =
      |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → K) : ℝ) /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)| *
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          |((Fintype.card ({ i : Fin q // i ∉ pairFamilyComponentVertices Γ C } → K) : ℝ)⁻¹)| *
            (((3 : ℝ) ^ (pairFamilyComponentEdgeFamily Γ C).card) *
              ((Fintype.card K : ℝ) ^
                  (2 * q - (pairFamilyComponentVertices Γ C).card) /
                (Fintype.card K : ℝ) ^ q)) := by
  unfold componentVisibleObstructionTermBudget
  congr 1
  refine Finset.prod_congr rfl ?_
  intro C _hC
  rw [componentLocalAtomizedRankBudget_const_rank (q := q) (K := K) Γ C
    (pairFamilyComponentVertices Γ C).card]
  rw [card_component_pairAtomChoiceFamily (q := q) Γ C]
  norm_num

theorem componentVisibleObstructionTermBudget_eq_complementNormalizer_mul_three_pow_card
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (Γ : Finset (PairEdge (coordinates q))) :
    componentVisibleObstructionTermBudget (q := q) (K := K) Γ =
      |(Fintype.card ({ i : Fin q // i ∉ edgeVertices Γ } → K) : ℝ) /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)| *
        (3 : ℝ) ^ Γ.card := by
  unfold componentVisibleObstructionTermBudget
  congr 1
  calc
    (∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        componentLocalAtomizedRankBudget (q := q) (K := K) Γ C
          (fun _choice => (pairFamilyComponentVertices Γ C).card)) =
        ∏ C : (pairFamilySupportGraph Γ).ConnectedComponent,
          (3 : ℝ) ^ (pairFamilyComponentEdgeFamily Γ C).card := by
          refine Finset.prod_congr rfl ?_
          intro C _hC
          exact componentLocalAtomizedRankBudget_visibleObstruction_eq_three_pow
            (q := q) (K := K) Γ C
    _ = (3 : ℝ) ^
          (∑ C : (pairFamilySupportGraph Γ).ConnectedComponent,
            (pairFamilyComponentEdgeFamily Γ C).card) := by
          rw [← Finset.prod_pow_eq_pow_sum Finset.univ
            (fun C : (pairFamilySupportGraph Γ).ConnectedComponent =>
              (pairFamilyComponentEdgeFamily Γ C).card) (3 : ℝ)]
    _ = (3 : ℝ) ^ Γ.card := by
          rw [sum_card_pairFamilyComponentEdgeFamily]

theorem componentVisibleObstructionTermBudget_eq_normalizerSlack_mul_three_pow_div_card_pow
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hq : q ≤ Fintype.card K) (Γ : Finset (PairEdge (coordinates q))) :
    componentVisibleObstructionTermBudget (q := q) (K := K) Γ =
      ((Fintype.card K : ℝ) ^ q /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
        ((3 : ℝ) ^ Γ.card /
          (Fintype.card K : ℝ) ^ (edgeVertices Γ).card) := by
  rw [componentVisibleObstructionTermBudget_eq_complementNormalizer_mul_three_pow_card
    (q := q) (K := K) Γ]
  rw [card_complement_function_space (q := q) (K := K) (edgeVertices Γ)]
  let N : ℝ := Fintype.card K
  let Z : ℝ := (visibleNormalizerNNReal (G := K) (q := q) : ℝ)
  let v : Nat := (edgeVertices Γ).card
  let m : Nat := Γ.card
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := K)
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hZ_pos : 0 < Z := by
    dsimp [Z]
    rw [NNReal.coe_pos]
    exact lt_of_le_of_ne bot_le
      (Ne.symm (visibleNormalizerNNReal_ne_zero (G := K) (q := q) hq))
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
  have hv_le : v ≤ q := by
    dsimp [v]
    simpa [coordinates] using Finset.card_le_card (edgeVertices_subset Γ)
  have hsub : q = q - v + v := by omega
  have hquot_pos : 0 < (N ^ (q - v)) / Z := div_pos (pow_pos hN_pos _) hZ_pos
  have hcast : ((Fintype.card K ^ (q - (edgeVertices Γ).card) : Nat) : ℝ) =
      N ^ (q - v) := by
    dsimp [N, v]
    norm_num
  rw [hcast]
  rw [abs_of_pos hquot_pos]
  rw [show (Fintype.card K : ℝ) = N by rfl]
  rw [show ((visibleNormalizerNNReal (G := K) (q := q) : NNReal) : ℝ) = Z by rfl]
  rw [show (edgeVertices Γ).card = v by rfl]
  rw [show Γ.card = m by rfl]
  rw [hsub, pow_add]
  field_simp [hN_ne, hZ_ne]
  have hpowexp : q - v + v - v = q - v := by omega
  rw [hpowexp]

/-- Endpoint using the concrete component visible-obstruction term budget.  The
remaining analytic obligation is now a single covering-family summability
premise over `componentVisibleObstructionTermBudget`. -/
theorem xop_advantageOn_injective_of_componentVisibleObstructionTermBudget_geTwo_pow_small_q
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (ε : NNReal) {activity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card K)
    (hvis : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      ∀ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∀ choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice,
          HasVisibleObstruction (q := q) K
            (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        (S.powerset.card : ℝ) *
          componentVisibleObstructionTermBudget (q := q) (K := K) Γ) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_componentLocalVisibleObstructionBudget_geTwo_pow_small_q
    (K := K) (q := q) ε
    (termBudget := componentVisibleObstructionTermBudget (q := q) (K := K))
    hq hvis ?_ hbudget ha hsmall hactivity hε
  intro Γ _hΓ
  rfl

/-- Endpoint using the graph-family weight exposed by
`componentVisibleObstructionTermBudget_eq_normalizerSlack_mul_three_pow_div_card_pow`.
This keeps the remaining covering summability obligation in the scalar form
`normalizerSlack * 3^|Γ| / |K|^|edgeVertices Γ|`. -/
theorem xop_advantageOn_injective_of_componentVisibleObstructionGraphWeight_geTwo_pow_small_q
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (ε : NNReal) {activity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card K)
    (hvis : ∀ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
      ∀ C : (pairFamilySupportGraph Γ).ConnectedComponent,
        ∀ choice : (e : {e // e ∈ pairFamilyComponentEdgeFamily Γ C}) → PairAtomChoice,
          HasVisibleObstruction (q := q) K
            (atomFamilyRow (pairAtomChoiceFamilyAtoms (pairFamilyComponentEdgeFamily Γ C) choice)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ),
        (S.powerset.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
              (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
            ((3 : ℝ) ^ Γ.card /
              (Fintype.card K : ℝ) ^ (edgeVertices Γ).card))) ≤ activity S.card)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), activity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_componentVisibleObstructionTermBudget_geTwo_pow_small_q
    (K := K) (q := q) ε hq hvis ?_ ha hsmall hactivity hε
  intro S hSpow hS hge
  calc
    (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      (S.powerset.card : ℝ) *
        componentVisibleObstructionTermBudget (q := q) (K := K) Γ)
        =
      (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      (S.powerset.card : ℝ) *
        (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
          ((3 : ℝ) ^ Γ.card /
            (Fintype.card K : ℝ) ^ (edgeVertices Γ).card))) := by
          refine Finset.sum_congr rfl ?_
          intro Γ _hΓ
          rw [componentVisibleObstructionTermBudget_eq_normalizerSlack_mul_three_pow_div_card_pow
            (q := q) (K := K) hq Γ]
    _ ≤ activity S.card := hbudget S hSpow hS hge

/-- A theorem-facing certificate for the still-missing Penrose/Ursell cumulant
construction.  It packages exactly what the rank side can consume: a genuine
pair-cluster contribution family, its cluster expansion, and an evaluation of
each contribution as a finite signed sum of hidden-solution fibers for selected
atom families. -/
structure PairClusterAtomizedContributionCertificate (K : Type*) [Field K]
    [Fintype K] [DecidableEq K] [Nonempty K] (q : Nat) where
  contribution : PairClusterContribution (G := K) (q := q)
  Term : (S : Finset (Fin q)) → PairCluster S → Type*
  termFintype : ∀ S (C : PairCluster S), Fintype (Term S C)
  coeff : ∀ {S : Finset (Fin q)} (C : PairCluster S), Term S C → ℝ
  atoms : ∀ {S : Finset (Fin q)} (C : PairCluster S), Term S C → Finset (Atom S)
  expansion : PairClusterExpansion (G := K) (q := q) contribution
  eval : ∀ S (C : PairCluster S) (y : Fin q → K),
    contribution S C y =
      ∑ t : Term S C,
        coeff C t *
          (Fintype.card {a : Fin q → K // AtomFamilyHolds y a (atoms C t)} : ℝ)

/-- The rank-budget expression generated by an atomized contribution
certificate.  It uses the certificate's finite term set explicitly, so theorem
statements consuming the certificate do not need separate local typeclass
instances for every dependent term type. -/
def atomizedContributionRankBudget [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (cert : PairClusterAtomizedContributionCertificate K q)
    {S : Finset (Fin q)} (C : PairCluster S)
    (rankBudget : cert.Term S C → Nat) : ℝ :=
  ∑ t ∈ (@Finset.univ (cert.Term S C) (cert.termFintype S C)),
    |cert.coeff C t| *
      ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
        (Fintype.card K : ℝ) ^ q)

/-- Atomized cumulant evaluations reduce a single contribution's visible `L¹`
norm to joint-rank budgets for the selected atom families in the certificate. -/
theorem visibleL1_contribution_le_sum_atomized_jointRankBudget
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (cert : PairClusterAtomizedContributionCertificate K q)
    {S : Finset (Fin q)} (C : PairCluster S)
    (rankBudget : cert.Term S C → Nat)
    (hvr : ∀ t, rankBudget t ≤
      jointRank (q := q) K (atomFamilyRow (cert.atoms C t))) :
    visibleL1 (G := K) (q := q) (cert.contribution S C) ≤
      atomizedContributionRankBudget (q := q) (K := K) cert C rankBudget := by
  classical
  letI := cert.termFintype S C
  unfold atomizedContributionRankBudget
  have heval :
      cert.contribution S C =
        fun y =>
          ∑ t : cert.Term S C,
            cert.coeff C t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (cert.atoms C t)} : ℝ) := by
    funext y
    exact cert.eval S C y
  rw [heval]
  calc
    visibleL1 (G := K) (q := q)
        (fun y =>
          ∑ t : cert.Term S C,
            cert.coeff C t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (cert.atoms C t)} : ℝ)) ≤
        ∑ t : cert.Term S C,
          visibleL1 (G := K) (q := q)
            (fun y =>
              cert.coeff C t *
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (cert.atoms C t)} : ℝ)) := by
          simpa using
            visibleL1_sum_le (G := K) (q := q)
              (Finset.univ : Finset (cert.Term S C))
              (fun t y =>
                cert.coeff C t *
                  (Fintype.card {a : Fin q → K //
                    AtomFamilyHolds y a (cert.atoms C t)} : ℝ))
    _ =
        ∑ t : cert.Term S C,
          |cert.coeff C t| *
            visibleL1 (G := K) (q := q)
              (fun y =>
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (cert.atoms C t)} : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [visibleL1_const_mul]
    _ ≤
        ∑ t : cert.Term S C,
          |cert.coeff C t| *
            ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
              (Fintype.card K : ℝ) ^ q) := by
          refine Finset.sum_le_sum ?_
          intro t _ht
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [visibleL1_atomFamily_solution_card_eq_uniformAverage (G := K) (q := q)]
          exact uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge
            (q := q) (K := K) (cert.atoms C t) (hvr t)

/-- A certificate-level selected-tree fiber budget supplies the `hfiber` premise
expected by `Mayer.pairClusterPenroseActivityBoundGeTwo_of_selectedContributionFiberBound`. -/
theorem selectedContributionFiberBound_of_atomizedCertificate
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    (cert : PairClusterAtomizedContributionCertificate K q)
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    (rankBudget : ∀ S (C : PairCluster S), cert.Term S C → Nat)
    (hvr : ∀ S (C : PairCluster S) (t : cert.Term S C),
      rankBudget S C t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms C t)))
    (hfiberBudget : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        atomizedContributionRankBudget (q := q) (K := K) cert C (rankBudget S C)) ≤
          treeCharge S T) :
    ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (cert.contribution S C)) ≤ treeCharge S T := by
  intro S hSpow hS T
  refine le_trans ?_ (hfiberBudget S hSpow hS T)
  refine Finset.sum_le_sum ?_
  intro C _hC
  exact visibleL1_contribution_le_sum_atomized_jointRankBudget
    (q := q) (K := K) cert C (rankBudget S C) (hvr S C)

/-- Final quadratic endpoint from an atomized Penrose/Ursell contribution
certificate.  The remaining mathematical leaves are now concrete: prove the
certificate, prove joint-rank budgets for its terms, and prove the selected
tree-fiber/local-activity estimates. -/
theorem xop_advantageOn_injective_of_atomizedCumulantCertificate_card_scaled_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (cert : PairClusterAtomizedContributionCertificate K q)
    (rankBudget : ∀ S (C : PairCluster S), cert.Term S C → Nat)
    (hq : q ≤ Fintype.card K)
    (hvr : ∀ S (C : PairCluster S) (t : cert.Term S C),
      rankBudget S C t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms C t)))
    (hfiberBudget : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        atomizedContributionRankBudget (q := q) (K := K) cert C (rankBudget S C)) ≤
          treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_selectedContributionFiberBound_card_scaled_quadratic
    (G := K) (q := q) (contribution := cert.contribution) (treeCharge := treeCharge)
    (localActivity := localActivity) (C := Cconst) hq cert.expansion
    (selectedContributionFiberBound_of_atomizedCertificate
      (q := q) (K := K) cert (treeCharge := treeCharge) rankBudget hvr hfiberBudget)
    hlocal hC hsmall hactivity

/-- Ge-two-only variant of the atomized cumulant certificate.  This is the
preferred target for a concrete Penrose/Ursell construction once the empty and
singleton ANOVA components have already been removed by the theorem spine. -/
structure PairClusterAtomizedContributionCertificateGeTwo (K : Type*) [Field K]
    [Fintype K] [DecidableEq K] [Nonempty K] (q : Nat) where
  contribution : PairClusterContribution (G := K) (q := q)
  Term : (S : Finset (Fin q)) → PairCluster S → Type*
  termFintype : ∀ S (C : PairCluster S), Fintype (Term S C)
  coeff : ∀ {S : Finset (Fin q)} (C : PairCluster S), Term S C → ℝ
  atoms : ∀ {S : Finset (Fin q)} (C : PairCluster S), Term S C → Finset (Atom S)
  expansion : PairClusterExpansionGeTwo (G := K) (q := q) contribution
  eval : ∀ S (C : PairCluster S) (y : Fin q → K),
    contribution S C y =
      ∑ t : Term S C,
        coeff C t *
          (Fintype.card {a : Fin q → K // AtomFamilyHolds y a (atoms C t)} : ℝ)

/-- Certified atom-choice family: a raw pair-Mayer atom-choice expansion term
plus the visible-obstruction certificate needed by the rank/codimension
endpoint.  The genuine ANOVA/Ursell construction must land in this type (or an
equivalent certified type), not in all raw `PairAtomChoice` families. -/
structure RankCertifiedPairAtomChoiceFamily (K : Type*) [Field K]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) where
  choice : (e : {e // e ∈ Γ}) → PairAtomChoice
  visibleObstruction :
    HasVisibleObstruction (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))

attribute [coe] RankCertifiedPairAtomChoiceFamily.choice

/-- A rank-certified atom-choice family is exactly a raw atom-choice family
equipped with a visible-obstruction certificate. -/
def rankCertifiedPairAtomChoiceFamilyEquivSubtype
    (K : Type*) [Field K] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    RankCertifiedPairAtomChoiceFamily (q := q) K Γ ≃
      {choice : ((e : {e // e ∈ Γ}) → PairAtomChoice) //
        HasVisibleObstruction (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))} where
  toFun t := ⟨t.choice, t.visibleObstruction⟩
  invFun t := ⟨t.1, t.2⟩
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro t
    cases t
    rfl

noncomputable instance rankCertifiedPairAtomChoiceFamilySubtypeFintype
    (K : Type*) [Field K] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    Fintype {choice : ((e : {e // e ∈ Γ}) → PairAtomChoice) //
      HasVisibleObstruction (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))} := by
  classical
  infer_instance

noncomputable instance rankCertifiedPairAtomChoiceFamilyFintype
    (K : Type*) [Field K] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    Fintype (RankCertifiedPairAtomChoiceFamily (q := q) K Γ) := by
  classical
  exact Fintype.ofEquiv
    {choice : ((e : {e // e ∈ Γ}) → PairAtomChoice) //
      HasVisibleObstruction (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))}
    ((rankCertifiedPairAtomChoiceFamilyEquivSubtype (q := q) K Γ).symm)

/-- A rank-certified atom-choice family over one pair edge must choose `both`.
The hidden-only and shifted-only singleton choices have no visible obstruction,
so they cannot inhabit `RankCertifiedPairAtomChoiceFamily`. -/
theorem rankCertifiedPairAtomChoiceFamily_singleton_choice_eq_both
    [Field K] {S : Finset (Fin q)} (e : PairEdge S)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :
    t.choice ⟨e, by simp⟩ = PairAtomChoice.both := by
  classical
  let e0 : {e' // e' ∈ ({e} : Finset (PairEdge S))} := ⟨e, by simp⟩
  have hvis := t.visibleObstruction
  have hfamily := pairAtomChoiceFamilyAtoms_singleton (q := q) e t.choice
  change pairAtomChoiceFamilyAtoms ({e} : Finset (PairEdge S)) t.choice =
      pairAtomChoiceAtoms e (t.choice e0) at hfamily
  rw [hfamily] at hvis
  cases hchoice : t.choice e0 with
  | hidden =>
      rw [hchoice] at hvis
      exact False.elim
        ((not_hasVisibleObstruction_pairAtomChoiceAtoms_hidden
          (q := q) (K := K) e) hvis)
  | shifted =>
      rw [hchoice] at hvis
      exact False.elim
        ((not_hasVisibleObstruction_pairAtomChoiceAtoms_shifted
          (q := q) (K := K) e) hvis)
  | both => rfl

/-- Canonical certified atom-choice family on a singleton edge: choose `both`.
-/
noncomputable def rankCertifiedPairAtomChoiceFamilySingletonBoth
    [Field K] {S : Finset (Fin q)} (e : PairEdge S) :
    RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S)) where
  choice := fun _ => PairAtomChoice.both
  visibleObstruction := by
    exact hasVisibleObstruction_of_pairAtomChoiceFamily_both
      (q := q) (K := K)
      (fun _ : {e' // e' ∈ ({e} : Finset (PairEdge S))} => PairAtomChoice.both)
      (e := e) (by simp) rfl

/-- The certified singleton atom-choice type has exactly the canonical `both`
term. -/
theorem rankCertifiedPairAtomChoiceFamily_singleton_eq
    [Field K] {S : Finset (Fin q)} (e : PairEdge S)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :
    t = rankCertifiedPairAtomChoiceFamilySingletonBoth (q := q) (K := K) e := by
  cases t with
  | mk choice hvis =>
      dsimp [rankCertifiedPairAtomChoiceFamilySingletonBoth]
      congr
      funext b
      have hb : b = ⟨e, by simp⟩ := by
        apply Subtype.ext
        exact Finset.mem_singleton.mp b.2
      rw [hb]
      exact rankCertifiedPairAtomChoiceFamily_singleton_choice_eq_both
        (q := q) (K := K) e ⟨choice, hvis⟩

/-- Certified singleton atom-choice families form a subsingleton. -/
theorem rankCertifiedPairAtomChoiceFamily_singleton_subsingleton
    [Field K] {S : Finset (Fin q)} (e : PairEdge S) :
    Subsingleton
      (RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) := by
  refine ⟨?_⟩
  intro t u
  rw [rankCertifiedPairAtomChoiceFamily_singleton_eq (q := q) (K := K) e t]
  rw [rankCertifiedPairAtomChoiceFamily_singleton_eq (q := q) (K := K) e u]

def rankCertifiedPairAtomChoiceFamilyCoeff (K : Type*) [Field K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ) : ℝ :=
  pairAtomChoiceFamilyCoeff t.choice

/-- The unique certified singleton atom-choice term has coefficient `1`. -/
theorem rankCertifiedPairAtomChoiceFamilyCoeff_singleton
    [Field K] {S : Finset (Fin q)} (e : PairEdge S)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :
    rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t = 1 := by
  classical
  unfold rankCertifiedPairAtomChoiceFamilyCoeff pairAtomChoiceFamilyCoeff
  have hchoice_all : ∀ b : {e' // e' ∈ ({e} : Finset (PairEdge S))},
      t.choice b = PairAtomChoice.both := by
    intro b
    have hb : b = ⟨e, by simp⟩ := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp b.2
    rw [hb]
    exact rankCertifiedPairAtomChoiceFamily_singleton_choice_eq_both
      (q := q) (K := K) e t
  simp [pairAtomChoiceCoeff, hchoice_all]

@[simp]
theorem abs_rankCertifiedPairAtomChoiceFamilyCoeff (K : Type*) [Field K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ) :
    |rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t| = (1 : ℝ) := by
  simp [rankCertifiedPairAtomChoiceFamilyCoeff]

/-- The visible-obstruction certificate only restricts the raw atom choices: a
certified atom-choice family injects into the raw three-choice family. -/
theorem card_rankCertifiedPairAtomChoiceFamily_le_three_pow
    (K : Type*) [Field K] {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    Fintype.card (RankCertifiedPairAtomChoiceFamily (q := q) K Γ) ≤ 3 ^ Γ.card := by
  classical
  let raw := (e : {e // e ∈ Γ}) → PairAtomChoice
  have hinj :
      Function.Injective
        (fun t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ => t.choice) := by
    intro t u h
    cases t
    cases u
    simp at h
    subst h
    rfl
  calc
    Fintype.card (RankCertifiedPairAtomChoiceFamily (q := q) K Γ) ≤ Fintype.card raw :=
      Fintype.card_le_of_injective _ hinj
    _ = 3 ^ Γ.card := by
      simpa [raw] using card_pairAtomChoiceFamily (q := q) Γ

def rankCertifiedPairAtomChoiceFamilyAtoms (K : Type*) [Field K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ) : Finset (Atom S) :=
  pairAtomChoiceFamilyAtoms Γ t.choice

/-- The unique certified singleton atom-choice term selects both atoms on the
edge. -/
theorem rankCertifiedPairAtomChoiceFamilyAtoms_singleton
    [Field K] {S : Finset (Fin q)} (e : PairEdge S)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :
    rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t = pairEdgeFullAtoms e := by
  classical
  unfold rankCertifiedPairAtomChoiceFamilyAtoms
  rw [pairAtomChoiceFamilyAtoms_singleton (q := q) e t.choice]
  rw [rankCertifiedPairAtomChoiceFamily_singleton_choice_eq_both
    (q := q) (K := K) e t]
  rfl

/-- Reindexing formula from certified atom-choice families to the corresponding
subtype of raw atom choices. -/
theorem sum_rankCertifiedPairAtomChoiceFamily_eq_subtype
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) (y : Fin q → K) :
    (∑ t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ,
      rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t *
        (Fintype.card {aS : S → K //
          AtomFamilyHoldsOn (q := q) y
            (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) aS} : ℝ)) =
    ∑ choice : {choice : ((e : {e // e ∈ Γ}) → PairAtomChoice) //
        HasVisibleObstruction (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))},
      pairAtomChoiceFamilyCoeff choice.1 *
        (Fintype.card {aS : S → K //
          AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice.1) aS} : ℝ) := by
  refine Fintype.sum_equiv
    (rankCertifiedPairAtomChoiceFamilyEquivSubtype (q := q) K Γ) _ _ ?_
  intro t
  rfl

/-- Under a nonempty ANOVA component, the sum over all raw atom choices equals
the sum over rank-certified choices: every raw choice without a visible
obstruction is killed by the constant-fiber cancellation lemma. -/
theorem anovaComponent_rawPairAtomChoiceFamily_sum_eq_rankCertified_sum
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hS : S.Nonempty) (Γ : Finset (PairEdge S)) :
    (fun y : Fin q → K =>
      ∑ choice : ((e : {e // e ∈ Γ}) → PairAtomChoice),
        anovaComponent S
          (fun y : Fin q → K =>
            pairAtomChoiceFamilyCoeff choice *
              (Fintype.card {aS : S → K //
                AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)) y) =
    (fun y : Fin q → K =>
      ∑ t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ,
        anovaComponent S
          (fun y : Fin q → K =>
            rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t *
              (Fintype.card {aS : S → K //
                AtomFamilyHoldsOn (q := q) y
                  (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) aS} : ℝ)) y) := by
  classical
  funext y
  let raw := ((e : {e // e ∈ Γ}) → PairAtomChoice)
  let p : raw → Prop := fun choice =>
    HasVisibleObstruction (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))
  let f : raw → (Fin q → K) → ℝ := fun choice y =>
    anovaComponent S
      (fun y : Fin q → K =>
        pairAtomChoiceFamilyCoeff choice *
          (Fintype.card {aS : S → K //
            AtomFamilyHoldsOn (q := q) y (pairAtomChoiceFamilyAtoms Γ choice) aS} : ℝ)) y
  have hzero : ∀ choice : raw, ¬ p choice → f choice y = 0 := by
    intro choice hno
    dsimp [f]
    rw [RandomSystems.Applications.XoP.ANOVA.anovaComponent_const_mul]
    rw [anovaComponent_atomChoiceFiber_eq_zero_of_not_hasVisibleObstruction'
      (q := q) (K := K) Γ choice hno hS]
    simp
  calc
    (∑ choice : raw, f choice y) = ∑ choice : {choice : raw // p choice}, f choice.1 y := by
      have hcompl : (∑ choice : {choice : raw // ¬ p choice}, f choice.1 y) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro choice _hchoice
        exact hzero choice.1 choice.2
      rw [← Fintype.sum_subtype_add_sum_subtype (p := p) (f := fun choice : raw => f choice y)]
      simp [hcompl]
    _ = ∑ t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ,
        anovaComponent S
          (fun y : Fin q → K =>
            rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t *
              (Fintype.card {aS : S → K //
                AtomFamilyHoldsOn (q := q) y
                  (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) aS} : ℝ)) y := by
      refine (Fintype.sum_equiv
        (rankCertifiedPairAtomChoiceFamilyEquivSubtype (q := q) K Γ) _ _ ?_).symm
      intro t
      rfl

theorem rankCertifiedPairAtomChoiceFamily_hasVisibleObstruction
    (K : Type*) [Field K] {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ) :
    HasVisibleObstruction (q := q) K
      (atomFamilyRow (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t)) :=
  t.visibleObstruction

theorem jointRank_rankCertifiedPairAtomChoiceFamily_ge_card_of_pairConnected
    [Field K] {S : Finset (Fin q)} (Γ : Finset (PairEdge S))
    (hconn : PairConnected Γ) {r : Fin q} (hr : r ∈ edgeVertices Γ)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K Γ) :
    (edgeVertices Γ).card ≤
      jointRank (q := q) K
        (atomFamilyRow (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t)) := by
  exact jointRank_pairAtomChoiceFamily_ge_card_of_pairConnected_and_visibleObstruction
    (q := q) (K := K) Γ t.choice hconn hr t.visibleObstruction

/-- Rank-certified choices over a support-retyped pair cluster touch exactly the
cluster support. -/
@[simp]
theorem atomVertices_rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges
    [Field K] {S : Finset (Fin q)} (C : PairCluster S)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C)) :
    atomVertices (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) = S := by
  rw [rankCertifiedPairAtomChoiceFamilyAtoms, atomVertices_pairAtomChoiceFamilyAtoms,
    Mayer.edgeVertices_pairClusterSupportEdges]

/-- Rank-certified choices over a support-retyped pair cluster inherit atom
connectivity from the cluster's pair-edge connectivity. -/
theorem rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges_connected
    [Field K] {S : Finset (Fin q)} (C : PairCluster S)
    (hS : S.Nonempty)
    (t : RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C)) :
    ∃ r,
      r ∈ atomVertices (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) ∧
      ∀ j ∈ atomVertices (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t),
        Relation.ReflTransGen
          (atomLinked (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t)) r j := by
  rcases hS with ⟨r, hrS⟩
  refine ⟨r, ?_, ?_⟩
  · simpa using hrS
  · intro j hj
    rw [rankCertifiedPairAtomChoiceFamilyAtoms] at hj ⊢
    have hrEdge : r ∈ edgeVertices (Mayer.pairClusterSupportEdges C) := by
      rw [Mayer.edgeVertices_pairClusterSupportEdges]
      exact hrS
    have hjEdge : j ∈ edgeVertices (Mayer.pairClusterSupportEdges C) := by
      simpa [atomVertices_pairAtomChoiceFamilyAtoms] using hj
    exact atomLinked_reflTransGen_pairAtomChoiceFamilyAtoms_of_edgeLinked_reflTransGen
      (Mayer.pairClusterSupportEdges C) t.choice
      (Mayer.pairClusterSupportEdges_pairConnected C r hrEdge j hjEdge)

/-- The theorem-facing certified signed block contribution.  This is not the
raw pair-Mayer block; it is the contribution after the still-open
ANOVA/Ursell-centering leaf has removed or repackaged all atom-choice terms
that do not carry a visible-obstruction certificate. -/
def rankCertifiedSignedPairMayerBlockContribution
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (S : Finset (Fin q)) (C : PairCluster S) (y : Fin q → K) : ℝ :=
  ∑ t : RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C),
    rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t *
      (Fintype.card {aS : S → K //
        AtomFamilyHoldsOn (q := q) y
          (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) aS} : ℝ)

/-- The certified signed block contribution is already expressed in the
block-local atomized-fiber form required by the normalized-Ursell endpoint. -/
theorem rankCertifiedSignedPairMayerBlockContribution_blockLocalEval
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → K) :
    rankCertifiedSignedPairMayerBlockContribution (q := q) K S C y =
      ∑ t : RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C),
        rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t *
          (Fintype.card {aS : S → K //
            AtomFamilyHoldsOn (q := q) y
              (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) aS} : ℝ) := by
  rfl

/-- If a connected block has one support-retyped pair edge, its certified
signed block contribution is the full hidden+shifted atom fiber for that edge.
-/
theorem rankCertifiedSignedPairMayerBlockContribution_of_supportEdges_singleton
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (C : PairCluster S) {e : PairEdge S}
    (hedges : Mayer.pairClusterSupportEdges C = ({e} : Finset (PairEdge S)))
    (y : Fin q → K) :
    rankCertifiedSignedPairMayerBlockContribution (q := q) K S C y =
      (Fintype.card {aS : S → K //
        AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} : ℝ) := by
  classical
  unfold rankCertifiedSignedPairMayerBlockContribution
  rw [hedges]
  letI : Subsingleton
      (RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :=
    rankCertifiedPairAtomChoiceFamily_singleton_subsingleton (q := q) (K := K) e
  letI : Inhabited
      (RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :=
    ⟨rankCertifiedPairAtomChoiceFamilySingletonBoth (q := q) (K := K) e⟩
  letI : Unique
      (RankCertifiedPairAtomChoiceFamily (q := q) K ({e} : Finset (PairEdge S))) :=
    { default := rankCertifiedPairAtomChoiceFamilySingletonBoth (q := q) (K := K) e
      uniq := fun t =>
        rankCertifiedPairAtomChoiceFamily_singleton_eq (q := q) (K := K) e t }
  simp [rankCertifiedPairAtomChoiceFamilyCoeff_singleton,
    rankCertifiedPairAtomChoiceFamilyAtoms_singleton]

/-- On a two-point support, every certified signed block is a full edge-atom
fiber for the unique support-retyped edge. -/
theorem exists_rankCertifiedSignedPairMayerBlockContribution_cardTwo_fullAtomFiber
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2) (C : PairCluster S)
    (y : Fin q → K) :
    ∃ e : PairEdge S,
      rankCertifiedSignedPairMayerBlockContribution (q := q) K S C y =
        (Fintype.card {aS : S → K //
          AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} : ℝ) := by
  rcases Mayer.exists_pairClusterSupportEdges_eq_singleton_of_support_card_eq_two
    (q := q) hcard C with ⟨e, hedges⟩
  refine ⟨e, ?_⟩
  exact rankCertifiedSignedPairMayerBlockContribution_of_supportEdges_singleton
    (q := q) (K := K) C hedges y

/-- Source-faithful signed local pair-Mayer blocks and theorem-facing
rank-certified blocks have the same nonempty ANOVA component.  This is the
formal bridge from raw signed pair-Mayer atomization to the certified
rank/codimension endpoint. -/
theorem anovaComponent_signedPairMayerBlockContribution_eq_rankCertified
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hS : S.Nonempty) (C : PairCluster S) :
    anovaComponent S (signedPairMayerBlockContribution (G := K) (q := q) S C) =
      anovaComponent S (rankCertifiedSignedPairMayerBlockContribution (q := q) K S C) := by
  classical
  have hsigned :
      signedPairMayerBlockContribution (G := K) (q := q) S C =
        fun y : Fin q → K =>
          ∑ choice : (e : {e // e ∈ Mayer.pairClusterSupportEdges C}) → PairAtomChoice,
            pairAtomChoiceFamilyCoeff choice *
              (Fintype.card {aS : S → K //
                AtomFamilyHoldsOn (q := q) y
                  (pairAtomChoiceFamilyAtoms (Mayer.pairClusterSupportEdges C) choice) aS} :
                ℝ) := by
    funext y
    exact signedPairMayerBlockContribution_blockLocalEval (G := K) (q := q) C y
  have hcert :
      rankCertifiedSignedPairMayerBlockContribution (q := q) K S C =
        fun y : Fin q → K =>
          ∑ t : RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C),
            rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t *
              (Fintype.card {aS : S → K //
                AtomFamilyHoldsOn (q := q) y
                  (rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t) aS} : ℝ) := by
    funext y
    exact rankCertifiedSignedPairMayerBlockContribution_blockLocalEval (K := K) (q := q) C y
  rw [hsigned, hcert]
  rw [anovaComponent_fintype_sum]
  rw [anovaComponent_fintype_sum]
  exact anovaComponent_rawPairAtomChoiceFamily_sum_eq_rankCertified_sum
    (q := q) (K := K) hS (Mayer.pairClusterSupportEdges C)

/-- Rank-budget expression for a ge-two-only atomized contribution certificate. -/
def atomizedContributionRankBudgetGeTwo [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (cert : PairClusterAtomizedContributionCertificateGeTwo K q)
    {S : Finset (Fin q)} (C : PairCluster S)
    (rankBudget : cert.Term S C → Nat) : ℝ :=
  ∑ t ∈ (@Finset.univ (cert.Term S C) (cert.termFintype S C)),
    |cert.coeff C t| *
      ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
        (Fintype.card K : ℝ) ^ q)

/-- The single-contribution `L¹` estimate for the ge-two certificate. -/
theorem visibleL1_contribution_le_sum_atomized_jointRankBudget_geTwo
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (cert : PairClusterAtomizedContributionCertificateGeTwo K q)
    {S : Finset (Fin q)} (C : PairCluster S)
    (rankBudget : cert.Term S C → Nat)
    (hvr : ∀ t, rankBudget t ≤
      jointRank (q := q) K (atomFamilyRow (cert.atoms C t))) :
    visibleL1 (G := K) (q := q) (cert.contribution S C) ≤
      atomizedContributionRankBudgetGeTwo (q := q) (K := K) cert C rankBudget := by
  classical
  letI := cert.termFintype S C
  unfold atomizedContributionRankBudgetGeTwo
  have heval :
      cert.contribution S C =
        fun y =>
          ∑ t : cert.Term S C,
            cert.coeff C t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (cert.atoms C t)} : ℝ) := by
    funext y
    exact cert.eval S C y
  rw [heval]
  calc
    visibleL1 (G := K) (q := q)
        (fun y =>
          ∑ t : cert.Term S C,
            cert.coeff C t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (cert.atoms C t)} : ℝ)) ≤
        ∑ t : cert.Term S C,
          visibleL1 (G := K) (q := q)
            (fun y =>
              cert.coeff C t *
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (cert.atoms C t)} : ℝ)) := by
          simpa using
            visibleL1_sum_le (G := K) (q := q)
              (Finset.univ : Finset (cert.Term S C))
              (fun t y =>
                cert.coeff C t *
                  (Fintype.card {a : Fin q → K //
                    AtomFamilyHolds y a (cert.atoms C t)} : ℝ))
    _ =
        ∑ t : cert.Term S C,
          |cert.coeff C t| *
            visibleL1 (G := K) (q := q)
              (fun y =>
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (cert.atoms C t)} : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [visibleL1_const_mul]
    _ ≤
        ∑ t : cert.Term S C,
          |cert.coeff C t| *
            ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
              (Fintype.card K : ℝ) ^ q) := by
          refine Finset.sum_le_sum ?_
          intro t _ht
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [visibleL1_atomFamily_solution_card_eq_uniformAverage (G := K) (q := q)]
          exact uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge
            (q := q) (K := K) (cert.atoms C t) (hvr t)

/-- Ge-two atomized certificates supply the selected-tree fiber premise expected
by the ge-two-only Penrose endpoint. -/
theorem selectedContributionFiberBound_of_atomizedCertificateGeTwo
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    (cert : PairClusterAtomizedContributionCertificateGeTwo K q)
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    (rankBudget : ∀ S (C : PairCluster S), cert.Term S C → Nat)
    (hvr : ∀ S (C : PairCluster S) (t : cert.Term S C),
      rankBudget S C t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms C t)))
    (hfiberBudget : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        atomizedContributionRankBudgetGeTwo (q := q) (K := K) cert C (rankBudget S C)) ≤
          treeCharge S T) :
    ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        visibleL1 (cert.contribution S C)) ≤ treeCharge S T := by
  intro S hSpow hS T
  refine le_trans ?_ (hfiberBudget S hSpow hS T)
  refine Finset.sum_le_sum ?_
  intro C _hC
  exact visibleL1_contribution_le_sum_atomized_jointRankBudget_geTwo
    (q := q) (K := K) cert C (rankBudget S C) (hvr S C)

/-- Final quadratic endpoint from a ge-two-only atomized Penrose/Ursell
certificate.  Compared with the full certificate endpoint, the concrete
construction now only needs to prove the cluster expansion on supports with
cardinality at least two. -/
theorem xop_advantageOn_injective_of_atomizedCumulantCertificateGeTwo_card_scaled_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {treeCharge : (S : Finset (Fin q)) → PairTree S → ℝ}
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (cert : PairClusterAtomizedContributionCertificateGeTwo K q)
    (rankBudget : ∀ S (C : PairCluster S), cert.Term S C → Nat)
    (hq : q ≤ Fintype.card K)
    (hvr : ∀ S (C : PairCluster S) (t : cert.Term S C),
      rankBudget S C t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms C t)))
    (hfiberBudget : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        atomizedContributionRankBudgetGeTwo (q := q) (K := K) cert C (rankBudget S C)) ≤
          treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  have hpenrose :
      PairClusterPenroseActivityBoundGeTwoOnly (G := K) (q := q)
        cert.contribution localActivity :=
    Mayer.pairClusterPenroseActivityBoundGeTwoOnly_of_selectedContributionFiberBound
      (G := K) (q := q) (contribution := cert.contribution) (treeCharge := treeCharge)
      (localActivity := localActivity) cert.expansion
      (selectedContributionFiberBound_of_atomizedCertificateGeTwo
        (q := q) (K := K) cert (treeCharge := treeCharge) rankBudget hvr hfiberBudget)
      hlocal
  refine Mayer.xop_advantageOn_injective_of_pairClusterPenroseActivityGeTwoOnly_Ico
    (G := K) (q := q)
    (Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2))
    hq hpenrose ?_
  have hactivity' : ∀ k ∈ Finset.Ico 2 ((coordinates q).card + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k := by
    simpa [coordinates] using hactivity
  refine le_trans
    (Mayer.sum_Ico_choose_mul_le_of_activity_le ((coordinates q).card) hactivity') ?_
  refine le_trans
    (Mayer.sum_Ico_choose_mul_pow_le_two_mul_sq ((coordinates q).card)
      (div_nonneg hC (Nat.cast_nonneg _)) (by simpa [coordinates] using hsmall)) ?_
  have hshape :
      2 * ((((coordinates q).card : ℝ) * (Cconst / (Fintype.card K : ℝ))) ^ 2) =
        2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2 := by
    simp [coordinates]
    ring
  rw [hshape]
  have hnonneg : 0 ≤ 2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2 := by
    positivity
  exact le_of_eq (Real.coe_toNNReal _ hnonneg).symm

/-- Ge-two atomized-certificate endpoint with a uniform per-tree fiber budget.
The tree-count factor is discharged by
`Mayer.pairTree_sum_le_two_pow_choose_mul`, so the remaining Penrose leaf is a
per-selected-tree estimate plus a scalar support-size activity bound. -/
theorem xop_advantageOn_injective_of_atomizedCumulantCertificateGeTwo_uniformTreeCharge_card_scaled_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (PairTree S)]
    {perTreeActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (cert : PairClusterAtomizedContributionCertificateGeTwo K q)
    (rankBudget : ∀ S (C : PairCluster S), cert.Term S C → Nat)
    (hq : q ≤ Fintype.card K)
    (hvr : ∀ S (C : PairCluster S) (t : cert.Term S C),
      rankBudget S C t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms C t)))
    (hperTree : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => pairClusterSpanningTree C hS = T),
        atomizedContributionRankBudgetGeTwo (q := q) (K := K) cert C (rankBudget S C)) ≤
          perTreeActivity S.card)
    (hper_nonneg : ∀ k, 0 ≤ perTreeActivity k)
    (hlocalBound : ∀ k, (2 ^ (k.choose 2) : ℝ) * perTreeActivity k ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_atomizedCumulantCertificateGeTwo_card_scaled_quadratic
    (K := K) (q := q) (treeCharge := fun S _T => perTreeActivity S.card)
    (localActivity := localActivity) (Cconst := Cconst) cert rankBudget hq hvr ?_ ?_
    hC hsmall hactivity
  · intro S hSpow hS T
    exact hperTree S hSpow hS T
  · intro S _hSpow _hS _hge
    exact le_trans
      (Mayer.pairTree_sum_le_two_pow_choose_mul (q := q) (S := S)
        (fun _T : PairTree S => perTreeActivity S.card)
        (hper_nonneg S.card) (fun _T => le_rfl))
      (by simpa using hlocalBound S.card)

/-- Support-indexed atomized certificate for the corrected Penrose/Ursell
route.  The index can encode a partition of the ANOVA support and products of
connected block contributions, avoiding the false single-cluster expansion
shape for `R - 1`. -/
structure SupportIndexedAtomizedContributionCertificateGeTwo (K : Type*) [Field K]
    [Fintype K] [DecidableEq K] [Nonempty K] (q : Nat)
    (Index : Finset (Fin q) → Type*) [∀ S : Finset (Fin q), Fintype (Index S)] where
  contribution : Mayer.SupportIndexedContribution (G := K) (q := q) Index
  Term : (S : Finset (Fin q)) → Index S → Type*
  termFintype : ∀ S (i : Index S), Fintype (Term S i)
  coeff : ∀ {S : Finset (Fin q)} (i : Index S), Term S i → ℝ
  atoms : ∀ {S : Finset (Fin q)} (i : Index S), Term S i → Finset (Atom S)
  expansion : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q) Index contribution
  eval : ∀ S (i : Index S) (y : Fin q → K),
    contribution S i y =
      ∑ t : Term S i,
        coeff i t *
          (Fintype.card {a : Fin q → K // AtomFamilyHolds y a (atoms i t)} : ℝ)

/-- Rank-budget expression for a support-indexed ge-two atomized certificate. -/
def supportIndexedAtomizedContributionRankBudgetGeTwo
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    (cert : SupportIndexedAtomizedContributionCertificateGeTwo K q Index)
    {S : Finset (Fin q)} (i : Index S)
    (rankBudget : cert.Term S i → Nat) : ℝ :=
  ∑ t ∈ (@Finset.univ (cert.Term S i) (cert.termFintype S i)),
    |cert.coeff i t| *
      ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
        (Fintype.card K : ℝ) ^ q)

/-- Local `L¹` estimate for any atomized hidden-fiber evaluation.  Unlike the
certificate wrapper below, this lemma does not require a global expansion
certificate; it is the single-index rank/codimension estimate needed by the
centered normalized-Ursell branch. -/
theorem visibleL1_atomized_eval_le_sum_jointRankBudget
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)}
    {Term : Type*} [Fintype Term]
    (f : (Fin q → K) → ℝ)
    (coeff : Term → ℝ) (atoms : Term → Finset (Atom S))
    (rankBudget : Term → Nat)
    (heval : f =
      fun y =>
        ∑ t : Term,
          coeff t *
            (Fintype.card {a : Fin q → K // AtomFamilyHolds y a (atoms t)} : ℝ))
    (hvr : ∀ t, rankBudget t ≤ jointRank (q := q) K (atomFamilyRow (atoms t))) :
    visibleL1 (G := K) (q := q) f ≤
      ∑ t : Term,
        |coeff t| *
          ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
            (Fintype.card K : ℝ) ^ q) := by
  rw [heval]
  calc
    visibleL1 (G := K) (q := q)
        (fun y =>
          ∑ t : Term,
            coeff t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (atoms t)} : ℝ)) ≤
        ∑ t : Term,
          visibleL1 (G := K) (q := q)
            (fun y =>
              coeff t *
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (atoms t)} : ℝ)) := by
          simpa using
            visibleL1_sum_le (G := K) (q := q)
              (Finset.univ : Finset Term)
              (fun t y =>
                coeff t *
                  (Fintype.card {a : Fin q → K //
                    AtomFamilyHolds y a (atoms t)} : ℝ))
    _ =
        ∑ t : Term,
          |coeff t| *
            visibleL1 (G := K) (q := q)
              (fun y =>
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (atoms t)} : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [visibleL1_const_mul]
    _ ≤
        ∑ t : Term,
          |coeff t| *
            ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
              (Fintype.card K : ℝ) ^ q) := by
          refine Finset.sum_le_sum ?_
          intro t _ht
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [visibleL1_atomFamily_solution_card_eq_uniformAverage (G := K) (q := q)]
          exact uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge
            (q := q) (K := K) (atoms t) (hvr t)

/-- Single-index `L¹` estimate for the support-indexed certificate. -/
theorem visibleL1_supportIndexedContribution_le_sum_atomized_jointRankBudget_geTwo
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    (cert : SupportIndexedAtomizedContributionCertificateGeTwo K q Index)
    {S : Finset (Fin q)} (i : Index S)
    (rankBudget : cert.Term S i → Nat)
    (hvr : ∀ t, rankBudget t ≤
      jointRank (q := q) K (atomFamilyRow (cert.atoms i t))) :
    visibleL1 (G := K) (q := q) (cert.contribution S i) ≤
      supportIndexedAtomizedContributionRankBudgetGeTwo
        (q := q) (K := K) cert i rankBudget := by
  classical
  letI := cert.termFintype S i
  unfold supportIndexedAtomizedContributionRankBudgetGeTwo
  have heval :
      cert.contribution S i =
        fun y =>
          ∑ t : cert.Term S i,
            cert.coeff i t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (cert.atoms i t)} : ℝ) := by
    funext y
    exact cert.eval S i y
  rw [heval]
  calc
    visibleL1 (G := K) (q := q)
        (fun y =>
          ∑ t : cert.Term S i,
            cert.coeff i t *
              (Fintype.card {a : Fin q → K //
                AtomFamilyHolds y a (cert.atoms i t)} : ℝ)) ≤
        ∑ t : cert.Term S i,
          visibleL1 (G := K) (q := q)
            (fun y =>
              cert.coeff i t *
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (cert.atoms i t)} : ℝ)) := by
          simpa using
            visibleL1_sum_le (G := K) (q := q)
              (Finset.univ : Finset (cert.Term S i))
              (fun t y =>
                cert.coeff i t *
                  (Fintype.card {a : Fin q → K //
                    AtomFamilyHolds y a (cert.atoms i t)} : ℝ))
    _ =
        ∑ t : cert.Term S i,
          |cert.coeff i t| *
            visibleL1 (G := K) (q := q)
              (fun y =>
                (Fintype.card {a : Fin q → K //
                  AtomFamilyHolds y a (cert.atoms i t)} : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [visibleL1_const_mul]
    _ ≤
        ∑ t : cert.Term S i,
          |cert.coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - rankBudget t) /
              (Fintype.card K : ℝ) ^ q) := by
          refine Finset.sum_le_sum ?_
          intro t _ht
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [visibleL1_atomFamily_solution_card_eq_uniformAverage (G := K) (q := q)]
          exact uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge
            (q := q) (K := K) (cert.atoms i t) (hvr t)

/-- Support-indexed atomized certificates feed the corrected support-indexed
activity interface. -/
theorem supportIndexedActivityBound_of_atomizedCertificateGeTwo
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    (cert : SupportIndexedAtomizedContributionCertificateGeTwo K q Index)
    {localActivity : Nat → ℝ}
    (rankBudget : ∀ S (i : Index S), cert.Term S i → Nat)
    (hvr : ∀ S (i : Index S) (t : cert.Term S i),
      rankBudget S i t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms i t)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Index S,
        supportIndexedAtomizedContributionRankBudgetGeTwo
          (q := q) (K := K) cert i (rankBudget S i)) ≤ localActivity S.card) :
    Mayer.SupportIndexedActivityBoundGeTwo (G := K) (q := q)
      Index cert.contribution localActivity := by
  intro S hSpow hS hge
  refine le_trans ?_ (hbudget S hSpow hS hge)
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact visibleL1_supportIndexedContribution_le_sum_atomized_jointRankBudget_geTwo
    (q := q) (K := K) cert i (rankBudget S i) (hvr S i)

/-- Final quadratic endpoint for the corrected support-indexed atomized
Penrose/Ursell certificate. -/
theorem xop_advantageOn_injective_of_supportIndexedAtomizedCertificateGeTwo_card_scaled_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {Index : Finset (Fin q) → Type*} [∀ S : Finset (Fin q), Fintype (Index S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (cert : SupportIndexedAtomizedContributionCertificateGeTwo K q Index)
    (rankBudget : ∀ S (i : Index S), cert.Term S i → Nat)
    (hq : q ≤ Fintype.card K)
    (hvr : ∀ S (i : Index S) (t : cert.Term S i),
      rankBudget S i t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms i t)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Index S,
        supportIndexedAtomizedContributionRankBudgetGeTwo
          (q := q) (K := K) cert i (rankBudget S i)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact Mayer.xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_card_scaled_quadratic
    (G := K) (q := q) (Index := Index) (contribution := cert.contribution)
    (localActivity := localActivity) (C := Cconst)
    hq cert.expansion
    (supportIndexedActivityBound_of_atomizedCertificateGeTwo
      (q := q) (K := K) cert (localActivity := localActivity) rankBudget hvr hbudget)
    hC hsmall hactivity

/-- Concrete support-partition atomized certificate target.  This is the
preferred formal object for the actual Penrose/Ursell construction: each index
is a partition of the ANOVA support together with connected data on every
block. -/
abbrev SupportPartitionClustersAtomizedContributionCertificateGeTwo
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (q : Nat) :=
  SupportIndexedAtomizedContributionCertificateGeTwo K q
    (Mayer.SupportPartitionClusters (q := q))

/-- Constructor for the concrete support-partition certificate from a global
atomized hidden-fiber evaluation.  The `heval` hypothesis is intentionally
global over the whole support-partition index; it must not be replaced by a
naive product of per-block full hidden-fiber counts. -/
noncomputable def supportPartitionClustersAtomizedCertificateGeTwo_of_globalAtomizedEval
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hexp : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
        blockContribution))
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ)) :
    SupportPartitionClustersAtomizedContributionCertificateGeTwo K q := by
  exact
    { contribution :=
        Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution
      Term := Term
      termFintype := termFintype
      coeff := coeff
      atoms := atoms
      expansion := hexp
      eval := heval }

/-- Direct quadratic endpoint from a global atomized hidden-fiber evaluation on
support-partition cluster products.  This is the concrete parent obligation for
the future Penrose/Ursell construction. -/
theorem xop_advantageOn_injective_of_supportPartitionClusters_globalAtomizedEval_card_scaled_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (rankBudget : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Nat)
    (hq : q ≤ Fintype.card K)
    (hexp : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
        blockContribution))
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hvr : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      rankBudget S i t ≤ jointRank (q := q) K (atomFamilyRow (atoms i t)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - rankBudget S i t) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  let cert :=
    supportPartitionClustersAtomizedCertificateGeTwo_of_globalAtomizedEval
      (q := q) (K := K) blockContribution Term termFintype coeff atoms hexp heval
  refine xop_advantageOn_injective_of_supportIndexedAtomizedCertificateGeTwo_card_scaled_quadratic
    (K := K) (q := q) (Index := Mayer.SupportPartitionClusters (q := q))
    (localActivity := localActivity) (Cconst := Cconst)
    cert rankBudget hq hvr ?_ hC hsmall hactivity
  intro S hSpow hS hge
  simpa [cert, supportIndexedAtomizedContributionRankBudgetGeTwo] using
    hbudget S hSpow hS hge

/-- Support-partition endpoint with the canonical rank budget `S.card`.
The rank side is discharged by block-local connectivity and visible
obstruction witnesses; the remaining hypothesis is the numerical activity
bound for those `S.card` budgets. -/
theorem xop_advantageOn_injective_of_supportPartitionClusters_globalAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (blockAtoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → (B : i.1.parts) → Finset (Atom B.1))
    (hq : q ≤ Fintype.card K)
    (hexp : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
        blockContribution))
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t = supportPartitionAtomFamily i.1 (blockAtoms i t))
    (hblocks : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i)
      (B : i.1.parts), atomVertices (blockAtoms i t B) = B.1)
    (hconn : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i)
      (B : i.1.parts), ∃ r,
        r ∈ atomVertices (blockAtoms i t B) ∧
        ∀ j ∈ atomVertices (blockAtoms i t B),
          Relation.ReflTransGen (atomLinked (blockAtoms i t B)) r j)
    (hvis : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i)
      (B : i.1.parts), HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms i t B)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_supportPartitionClusters_globalAtomizedEval_card_scaled_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms
    (fun S _i _t => S.card) hq hexp heval ?_ ?_ hC hsmall hactivity
  · intro S i t
    exact jointRank_ge_card_of_supportPartitionClusterBlockAtoms (q := q) (K := K)
      i (atoms i t) (blockAtoms i t) (hatoms S i t)
      (hblocks S i t) (hconn S i t) (hvis S i t)
  · intro S hSpow hS hge
    simpa using hbudget S hSpow hS hge

/-- Final quadratic endpoint for the concrete support-partition atomized
certificate. -/
theorem xop_advantageOn_injective_of_supportPartitionClustersAtomizedCertificateGeTwo_card_scaled_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (cert : SupportPartitionClustersAtomizedContributionCertificateGeTwo K q)
    (rankBudget : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      cert.Term S i → Nat)
    (hq : q ≤ Fintype.card K)
    (hvr : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : cert.Term S i),
      rankBudget S i t ≤ jointRank (q := q) K (atomFamilyRow (cert.atoms i t)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        supportIndexedAtomizedContributionRankBudgetGeTwo
          (q := q) (K := K) cert i (rankBudget S i)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_supportIndexedAtomizedCertificateGeTwo_card_scaled_quadratic
    (K := K) (q := q) (Index := Mayer.SupportPartitionClusters (q := q))
    (localActivity := localActivity) (Cconst := Cconst)
    cert rankBudget hq hvr hbudget hC hsmall hactivity

/-- Pair-family hidden sums are bounded by the hidden-rank budgets of the selected
atom-choice families.  The next theorem-forced step is to prove graph-specific
lower bounds on those hidden ranks for the actual Penrose-selected choices. -/
theorem abs_pairFamilyTerm_le_sum_atomChoiceFamily_hiddenRankBudget
    [Field K] [Fintype K] [DecidableEq K] {S : Finset (Fin q)}
    (Γ : Finset (PairEdge S)) (y : Fin q → K) :
    |pairFamilyTerm (G := K) Γ y| ≤
      ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        (Fintype.card K : ℝ) ^
          (q - hiddenRank (q := q) K (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))) := by
  rw [pairFamilyTerm_eq_sum_atomChoiceFamily_counts (G := K) (q := q) Γ y]
  calc
    |∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
        pairAtomChoiceFamilyCoeff choice *
          (Fintype.card {a : Fin q → K //
            AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ)| ≤
        ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          |pairAtomChoiceFamilyCoeff choice *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          (Fintype.card {a : Fin q → K //
            AtomFamilyHolds y a (pairAtomChoiceFamilyAtoms Γ choice)} : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro choice _hchoice
          simp [abs_mul]
    _ ≤ ∑ choice : (e : {e // e ∈ Γ}) → PairAtomChoice,
          (Fintype.card K : ℝ) ^
            (q - hiddenRank (q := q) K
              (atomFamilyRow (pairAtomChoiceFamilyAtoms Γ choice))) := by
          exact Finset.sum_le_sum (fun choice _ =>
            atomFamily_solution_card_real_le_pow_hiddenRank
              (q := q) (K := K) (pairAtomChoiceFamilyAtoms Γ choice) y)

theorem hiddenAtom_mem_pairFamilyFullAtoms {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {e : PairEdge S} (he : e ∈ Γ) :
    hiddenAtom e ∈ pairFamilyFullAtoms Γ := by
  rw [pairFamilyFullAtoms]
  exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩

theorem shiftedAtom_mem_pairFamilyFullAtoms {S : Finset (Fin q)} {Γ : Finset (PairEdge S)}
    {e : PairEdge S} (he : e ∈ Γ) :
    shiftedAtom e ∈ pairFamilyFullAtoms Γ := by
  rw [pairFamilyFullAtoms]
  exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩

@[simp]
theorem atomVertices_pairFamilyFullAtoms {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) :
    atomVertices (pairFamilyFullAtoms Γ) = edgeVertices Γ := by
  ext i
  simp only [atomVertices, pairFamilyFullAtoms, edgeVertices, pairEdgeFullAtoms,
    Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨atom, ⟨e, he, hhidden | hshifted⟩, hi⟩
    · subst hhidden
      exact ⟨e, he, hi⟩
    · subst hshifted
      exact ⟨e, he, hi⟩
  · rintro ⟨e, he, hi⟩
    exact ⟨hiddenAtom e, ⟨e, he, Or.inl rfl⟩, hi⟩

/-- Pair-edge adjacency embeds into atom adjacency after full atomization. -/
theorem edgeLinked_to_atomLinked_pairFamilyFullAtoms {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {i j : Fin q}
    (h : edgeLinked Γ i j) :
    atomLinked (pairFamilyFullAtoms Γ) i j := by
  rcases h with ⟨e, he, hdir⟩
  exact ⟨hiddenAtom e, hiddenAtom_mem_pairFamilyFullAtoms he, hdir⟩

/-- Pair-edge reachability embeds into atom reachability after full
atomization. -/
theorem reachable_edgeLinked_to_atomLinked_pairFamilyFullAtoms {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {i j : Fin q}
    (h : Relation.ReflTransGen (edgeLinked Γ) i j) :
    Relation.ReflTransGen (atomLinked (pairFamilyFullAtoms Γ)) i j := by
  exact h.mono (fun _ _ hxy => edgeLinked_to_atomLinked_pairFamilyFullAtoms (q := q) hxy)

/-- Each full-atomized pair edge contains its own hidden connection. -/
theorem hiddenAtomLinked_pairFamilyFullAtoms_self {S : Finset (Fin q)}
    {Γ : Finset (PairEdge S)} {e : PairEdge S} (he : e ∈ Γ) :
    hiddenAtomLinked (pairFamilyFullAtoms Γ) e.1.1 e.1.2 := by
  exact ⟨e, hiddenAtom_mem_pairFamilyFullAtoms he, Or.inl ⟨rfl, rfl⟩⟩

/-- Nonempty full atomizations always contain a concrete visible-obstruction
witness: a shifted atom closes against its own hidden atom. -/
theorem hasVisibleObstruction_pairFamilyFullAtoms_of_nonempty [Field K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)} (hΓ : Γ.Nonempty) :
    HasVisibleObstruction (q := q) K (atomFamilyRow (pairFamilyFullAtoms Γ)) := by
  rcases hΓ with ⟨e, he⟩
  exact hasVisibleObstruction_of_shiftedAtom_hiddenReachable (q := q) (K := K)
    (pairFamilyFullAtoms Γ) (shiftedAtom_mem_pairFamilyFullAtoms he)
    (Relation.ReflTransGen.single (hiddenAtomLinked_pairFamilyFullAtoms_self (q := q) he))

/-- The full atomization of a block cluster touches exactly that block.

This is a concrete adapter for the support-partition rank-budget endpoint: if a
future Penrose/Ursell term chooses the full hidden/shifted atomization of each
block cluster, the block-support hypothesis is already discharged by the
cluster support equation. -/
@[simp]
theorem atomVertices_supportPartitionCluster_fullAtoms
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (B : i.1.parts) :
    atomVertices (pairFamilyFullAtoms (i.2 B).edges) = B.1 := by
  rw [atomVertices_pairFamilyFullAtoms, (i.2 B).support_eq]

/-- Full atomization of a block cluster inherits connected atom reachability from
the block's pair-edge connectedness. -/
theorem supportPartitionCluster_fullAtoms_connected
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (B : i.1.parts) :
    ∃ r,
      r ∈ atomVertices (pairFamilyFullAtoms (i.2 B).edges) ∧
      ∀ j ∈ atomVertices (pairFamilyFullAtoms (i.2 B).edges),
        Relation.ReflTransGen
          (atomLinked (pairFamilyFullAtoms (i.2 B).edges)) r j := by
  rcases Mayer.supportPartitionClusters_block_nonempty (q := q) i B with ⟨r, hrB⟩
  refine ⟨r, ?_, ?_⟩
  · rw [atomVertices_pairFamilyFullAtoms, (i.2 B).support_eq]
    exact hrB
  · intro j hj
    have hrEdge : r ∈ edgeVertices (i.2 B).edges := by
      rw [(i.2 B).support_eq]
      exact hrB
    have hjEdge : j ∈ edgeVertices (i.2 B).edges := by
      simpa using hj
    exact reachable_edgeLinked_to_atomLinked_pairFamilyFullAtoms (q := q)
      ((i.2 B).connected r hrEdge j hjEdge)

/-- Full atomization of a nonempty support-partition block has a visible
obstruction. -/
theorem hasVisibleObstruction_supportPartitionCluster_fullAtoms [Field K]
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (B : i.1.parts) :
    HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairFamilyFullAtoms (i.2 B).edges)) := by
  have hB : B.1.Nonempty := Mayer.supportPartitionClusters_block_nonempty (q := q) i B
  exact hasVisibleObstruction_pairFamilyFullAtoms_of_nonempty (q := q) (K := K)
    (Mayer.pairCluster_edges_nonempty_of_support_nonempty (i.2 B) hB)

/-- The support-retyped full atomization of a block cluster touches exactly the
block.  This is the version whose atom family lives over `Atom B.1`, so it can
feed `supportPartitionAtomFamily`. -/
@[simp]
theorem atomVertices_supportPartitionCluster_supportFullAtoms
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (B : i.1.parts) :
    atomVertices (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))) = B.1 := by
  rw [atomVertices_pairFamilyFullAtoms, Mayer.edgeVertices_pairClusterSupportEdges]

/-- The support-retyped full atomization of a block cluster is connected in
the atom graph. -/
theorem supportPartitionCluster_supportFullAtoms_connected
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (B : i.1.parts) :
    ∃ r,
      r ∈ atomVertices (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))) ∧
      ∀ j ∈ atomVertices (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))),
        Relation.ReflTransGen
          (atomLinked (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B)))) r j := by
  rcases Mayer.supportPartitionClusters_block_nonempty (q := q) i B with ⟨r, hrB⟩
  refine ⟨r, ?_, ?_⟩
  · simpa using hrB
  · intro j hj
    have hrEdge : r ∈ edgeVertices (Mayer.pairClusterSupportEdges (i.2 B)) := by
      rw [Mayer.edgeVertices_pairClusterSupportEdges]
      exact hrB
    have hjEdge : j ∈ edgeVertices (Mayer.pairClusterSupportEdges (i.2 B)) := by
      simpa using hj
    exact reachable_edgeLinked_to_atomLinked_pairFamilyFullAtoms (q := q)
      (Mayer.pairClusterSupportEdges_pairConnected (i.2 B) r hrEdge j hjEdge)

/-- The support-retyped full atomization of a nonempty support-partition block
has a visible obstruction. -/
theorem hasVisibleObstruction_supportPartitionCluster_supportFullAtoms [Field K]
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (B : i.1.parts) :
    HasVisibleObstruction (q := q) K
      (atomFamilyRow (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B)))) := by
  have hB : B.1.Nonempty := Mayer.supportPartitionClusters_block_nonempty (q := q) i B
  exact hasVisibleObstruction_pairFamilyFullAtoms_of_nonempty (q := q) (K := K)
    (Mayer.pairClusterSupportEdges_nonempty_of_support_nonempty (i.2 B) hB)

/-- The global support-partition full atom family holds exactly when every
support-retyped edge in every block satisfies both the hidden and shifted
collision equations. -/
theorem atomFamilyHolds_supportPartition_supportFullAtoms_iff [AddGroup G] [DecidableEq G]
    {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) (y a : Fin q → G) :
    AtomFamilyHolds y a
        (supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B)))) ↔
      ∀ B : i.1.parts, ∀ e ∈ Mayer.pairClusterSupportEdges (i.2 B),
        pairBadHidden a e.1 ∧ pairBadShifted y a e.1 := by
  rw [atomFamilyHolds_supportPartitionAtomFamily_iff]
  constructor
  · intro h B
    exact (atomFamilyHolds_pairFamilyFullAtoms_iff (G := G)
      (Mayer.pairClusterSupportEdges (i.2 B)) y a).mp (h B)
  · intro h B
    exact (atomFamilyHolds_pairFamilyFullAtoms_iff (G := G)
      (Mayer.pairClusterSupportEdges (i.2 B)) y a).mpr (h B)

/-- Generic support-partition endpoint specialized to support-retyped full
atomization on every block.

Unlike `supportPartitionClusterProductContribution`, this accepts an arbitrary
support-indexed contribution on `SupportPartitionClusters`, so a future
Penrose/Ursell construction can carry coefficients depending on the whole
partition. -/
theorem xop_advantageOn_injective_of_supportPartitionContribution_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (contribution : Mayer.SupportIndexedContribution (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q)))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hexp : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q)) contribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      contribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  let cert : SupportPartitionClustersAtomizedContributionCertificateGeTwo K q :=
    { contribution := contribution
      Term := Term
      termFintype := termFintype
      coeff := @coeff
      atoms := @atoms
      expansion := hexp
      eval := heval }
  refine xop_advantageOn_injective_of_supportIndexedAtomizedCertificateGeTwo_card_scaled_quadratic
    (K := K) (q := q) (Index := Mayer.SupportPartitionClusters (q := q))
    (localActivity := localActivity) (Cconst := Cconst)
    cert (fun S _i _t => S.card) hq ?_ ?_ hC hsmall hactivity
  · intro S i t
    exact jointRank_ge_card_of_supportPartitionClusterBlockAtoms (q := q) (K := K)
      i (atoms i t)
      (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B)))
      (hatoms S i t)
      (fun B => atomVertices_supportPartitionCluster_supportFullAtoms (q := q) i B)
      (fun B => supportPartitionCluster_supportFullAtoms_connected (q := q) i B)
      (fun B => hasVisibleObstruction_supportPartitionCluster_supportFullAtoms
        (q := q) (K := K) i B)
  · intro S hSpow hS hge
    simpa [cert, supportIndexedAtomizedContributionRankBudgetGeTwo] using
      hbudget S hSpow hS hge

/-- Support-partition endpoint specialized to support-retyped full atomization on
every block.

This is the next theorem-facing adapter for the concrete Penrose/Ursell
construction: once its global evaluation terms use the blockwise full
hidden/shifted atom families, the rank-budget hypotheses are automatic.  The
remaining obligations are exactly the expansion, global evaluation, and scalar
activity budget. -/
theorem xop_advantageOn_injective_of_supportPartitionClusters_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hexp : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
        blockContribution))
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_supportPartitionClusters_globalAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms
    (fun {_S} i _t B => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B)))
    hq hexp heval hatoms ?_ ?_ ?_ hbudget hC hsmall hactivity
  · intro S i t B
    exact atomVertices_supportPartitionCluster_supportFullAtoms (q := q) i B
  · intro S i t B
    exact supportPartitionCluster_supportFullAtoms_connected (q := q) i B
  · intro S i t B
    exact hasVisibleObstruction_supportPartitionCluster_supportFullAtoms (q := q) (K := K) i B

/-- Same support-full-atomized endpoint, but with the source-faithful
component-factorized resummation premise in place of an already-packaged
`SupportIndexedExpansionGeTwo` proof. -/
theorem xop_advantageOn_injective_of_componentFactorized_resummation_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
      fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S idx y)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_supportPartitionClusters_globalSupportFullAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms hq
    (Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_supportPartition_resummation
      (G := K) (q := q) blockContribution hresum)
    heval hatoms hbudget hC hsmall hactivity

/-- Weighted-resummation version of the support-full-atomized endpoint.  This
is the preferred theorem-facing shape if the concrete Ursell/Penrose
construction supplies a partition-level Möbius coefficient. -/
theorem xop_advantageOn_injective_of_componentFactorized_weightedResummation_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (weight : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
      fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
          weight blockContribution S idx y)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
          weight blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_supportPartitionContribution_globalSupportFullAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
      weight blockContribution)
    Term termFintype coeff atoms hq
    (Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_weightedSupportPartition_resummation
      (G := K) (q := q) weight blockContribution hresum)
    heval hatoms hbudget hC hsmall hactivity

/-- Weighted support-partition endpoint from block-local signed atomized
evaluations.  This is the corrected replacement for the rejected
`supportFullAtomizedBlockContribution` route: the resummation is weighted, the
block contribution may be signed, and rank/codimension enters term-by-term
through block-local vertex/connectivity/visible-obstruction certificates. -/
theorem xop_advantageOn_injective_of_weightedResummation_blockLocalSignedAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (weight : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → ℝ)
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (BlockTerm : {S : Finset (Fin q)} → PairCluster S → Type*)
    [blockTermFintype : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      Fintype (BlockTerm C)]
    (blockCoeff : ∀ {S : Finset (Fin q)} (C : PairCluster S), BlockTerm C → ℝ)
    (blockAtoms : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      BlockTerm C → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionWeightedResummationGeTwo (G := K) (q := q)
      weight blockContribution)
    (hblockEval : ∀ {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → K),
      blockContribution S C y =
        ∑ tB : BlockTerm C,
          blockCoeff C tB *
            (Fintype.card {aS : S → K //
              AtomFamilyHoldsOn (q := q) y (blockAtoms C tB) aS} : ℝ))
    (hblocks : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S)
      (t : (B : i.1.parts) → BlockTerm (i.2 B)) (B : i.1.parts),
      atomVertices (blockAtoms (i.2 B) (t B)) = B.1)
    (hconn : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S)
      (t : (B : i.1.parts) → BlockTerm (i.2 B)) (B : i.1.parts), ∃ r,
        r ∈ atomVertices (blockAtoms (i.2 B) (t B)) ∧
        ∀ j ∈ atomVertices (blockAtoms (i.2 B) (t B)),
          Relation.ReflTransGen (atomLinked (blockAtoms (i.2 B) (t B))) r j)
    (hvis : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S)
      (t : (B : i.1.parts) → BlockTerm (i.2 B)) (B : i.1.parts),
        HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms (i.2 B) (t B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ ((B : i.1.parts) → BlockTerm (i.2 B))
            (by infer_instance)),
          |weight S i *
              ((∏ B : i.1.parts, blockCoeff (i.2 B) (t B)) /
                (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  let Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type _ :=
    fun _S i => (B : i.1.parts) → BlockTerm (i.2 B)
  let termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i) := by
    intro S i
    dsimp [Term]
    infer_instance
  let coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ :=
    fun {S} i t =>
      weight S i *
        ((∏ B : i.1.parts, blockCoeff (i.2 B) (t B)) /
          (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))
  let atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S) :=
    fun {_S} i t =>
      supportPartitionAtomFamily i.1
        (fun B : i.1.parts => blockAtoms (i.2 B) (t B))
  let contribution := Mayer.supportPartitionWeightedClusterProductContribution
    (G := K) (q := q) weight blockContribution
  have hexp : Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q)) contribution := by
    dsimp [contribution]
    exact Mayer.supportIndexedExpansionGeTwo_of_weightedResummationGeTwo
      (G := K) (q := q) weight blockContribution hresum
  have heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      contribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K // AtomFamilyHolds y a (atoms i t)} : ℝ) := by
    intro S i y
    dsimp [contribution]
    rw [Mayer.supportPartitionWeightedClusterProductContribution]
    have hunweighted := supportPartitionClusterProductContribution_eq_sum_pi_blockLocalAtomized
      (q := q) (K := K) blockContribution BlockTerm blockCoeff blockAtoms hblockEval i y
    rw [hunweighted]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    dsimp [coeff, atoms]
    ring
  let cert : SupportIndexedAtomizedContributionCertificateGeTwo K q
      (Mayer.SupportPartitionClusters (q := q)) :=
    { contribution := contribution
      Term := Term
      termFintype := termFintype
      coeff := @coeff
      atoms := @atoms
      expansion := hexp
      eval := heval }
  refine xop_advantageOn_injective_of_supportIndexedAtomizedCertificateGeTwo_card_scaled_quadratic
    (K := K) (q := q) (Index := Mayer.SupportPartitionClusters (q := q))
    (localActivity := localActivity) (Cconst := Cconst)
    cert (fun S _i _t => S.card) hq ?_ ?_ hC hsmall hactivity
  · intro S i t
    dsimp [cert, atoms]
    exact jointRank_ge_card_of_supportPartitionClusterBlockAtoms (q := q) (K := K)
      i (supportPartitionAtomFamily i.1 (fun B : i.1.parts => blockAtoms (i.2 B) (t B)))
      (fun B : i.1.parts => blockAtoms (i.2 B) (t B)) rfl
      (fun B : i.1.parts => hblocks i t B)
      (fun B : i.1.parts => hconn i t B)
      (fun B : i.1.parts => hvis i t B)
  · intro S hSpow hS hge
    dsimp [cert, supportIndexedAtomizedContributionRankBudgetGeTwo, coeff]
    simpa using hbudget S hSpow hS hge

/-- Source-normalized Ursell weight for the corrected support-partition branch.
It combines the partition-lattice Ursell coefficient with the global
component-factorized normalization factor already present in
`componentFactorizedNormalizedPairFamilyTerm`. -/
def supportPartitionNormalizedUrsellWeight
    (K : Type*) [AddGroup K] [Fintype K] [DecidableEq K]
    (S : Finset (Fin q)) (idx : Mayer.SupportPartitionClusters (q := q) S) : ℝ :=
  Mayer.supportPartitionUrsellWeight (q := q) S idx *
    ((Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) /
      (visibleNormalizerNNReal (G := K) (q := q) : ℝ))

/-- On a two-point support, every admissible support-partition index has one
block, so the bare Ursell coefficient is `1` and the normalized coefficient is
just the complement normalizer. -/
theorem supportPartitionNormalizedUrsellWeight_cardTwo
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : Mayer.SupportPartitionClusters (q := q) S) :
    supportPartitionNormalizedUrsellWeight (q := q) K S idx =
      (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) /
        (visibleNormalizerNNReal (G := K) (q := q) : ℝ) := by
  have hparts :
      idx.1.parts.card = 1 :=
    Mayer.supportPartitionClusters_parts_card_eq_one_of_support_card_eq_two
      (q := q) hcard idx
  simp [supportPartitionNormalizedUrsellWeight, Mayer.supportPartitionUrsellWeight, hparts]

/-- Two-point support-partition contributions collapse to the unique certified
block times the source normalizer factor. -/
theorem supportPartitionWeightedRankCertifiedContribution_cardTwo
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : Mayer.SupportPartitionClusters (q := q) S) (B : idx.1.parts)
    (y : Fin q → K) :
    Mayer.supportPartitionWeightedClusterProductContribution
        (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
        (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y =
      ((Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) /
        (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
        rankCertifiedSignedPairMayerBlockContribution (q := q) K B.1 (idx.2 B) y := by
  classical
  rw [Mayer.supportPartitionWeightedClusterProductContribution]
  rw [supportPartitionNormalizedUrsellWeight_cardTwo (q := q) K hcard idx]
  rw [Mayer.supportPartitionClusterProductContribution_cardTwo
    (G := K) (q := q)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K) hcard idx B y]

/-- Two-point support-partition contribution collapse, using the canonical
unique block chosen from the support-partition index. -/
theorem supportPartitionWeightedRankCertifiedContribution_cardTwo_uniqueBlock
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K) :
    Mayer.supportPartitionWeightedClusterProductContribution
        (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
        (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y =
      ((Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) /
        (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
        rankCertifiedSignedPairMayerBlockContribution (q := q) K
          (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx).1
          (idx.2 (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo
            (q := q) hcard idx)) y := by
  exact supportPartitionWeightedRankCertifiedContribution_cardTwo
    (q := q) (K := K) hcard idx
    (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx) y

/-- Two-point support-side contribution evaluated down to a full edge-atom
fiber.  This packages the base-branch support-partition simplifications while
leaving the covering-family contraction itself as the remaining obligation. -/
theorem exists_supportPartitionWeightedRankCertifiedContribution_cardTwo_fullAtomFiber
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K) :
    ∃ e : PairEdge
        (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx).1,
      Mayer.supportPartitionWeightedClusterProductContribution
          (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
          (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y =
        ((Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
          (Fintype.card {aS :
              (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo
                (q := q) hcard idx).1 → K //
            AtomFamilyHoldsOn (q := q) y (pairEdgeFullAtoms e) aS} : ℝ) := by
  classical
  let B := Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx
  rw [supportPartitionWeightedRankCertifiedContribution_cardTwo
    (q := q) (K := K) hcard idx B y]
  have hBcard : B.1.card = 2 := by
    rw [Mayer.supportPartitionClusters_block_eq_support_of_card_eq_two
      (q := q) hcard idx B]
    exact hcard
  rcases exists_rankCertifiedSignedPairMayerBlockContribution_cardTwo_fullAtomFiber
    (q := q) (K := K) hBcard (idx.2 B) y with ⟨e, he⟩
  refine ⟨e, ?_⟩
  rw [he]

/-- Two-point support-side contribution as a scalar multiple of the visible
collision indicator.  This is the concrete base-case form exposed by the full
hidden/shifted atom-fiber calculation. -/
theorem exists_supportPartitionWeightedRankCertifiedContribution_cardTwo_collisionIndicator
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (hcard : S.card = 2)
    (idx : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K) :
    ∃ e : PairEdge
        (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx).1,
      Mayer.supportPartitionWeightedClusterProductContribution
          (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
          (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y =
        ((Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) *
          (if y e.1.1 = y e.1.2 then (Fintype.card K : ℝ) else 0) := by
  classical
  rcases exists_supportPartitionWeightedRankCertifiedContribution_cardTwo_fullAtomFiber
    (q := q) (K := K) hcard idx y with ⟨e, he⟩
  refine ⟨e, ?_⟩
  have hBcard :
      (Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo (q := q) hcard idx).1.card = 2 := by
    rw [Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo_support
      (q := q) hcard idx]
    exact hcard
  rw [he]
  have hfiber := card_pairEdgeFullAtoms_cardTwo (q := q) hBcard e y
  rw [hfiber]
  by_cases hy : y e.1.1 = y e.1.2 <;> simp [hy]

/-- The remaining normalized, rank-certified resummation obligation on the
strongest quadratic-bound path. -/
def RankCertifiedNormalizedUrsellCoveringFiberResummation
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)] :
    Prop :=
  Mayer.SupportPartitionWeightedCoveringFiberResummationGeTwo (G := K) (q := q)
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)

/-- Source-faithful ambient form of the remaining normalized, rank-certified
resummation obligation.  This avoids forcing a covering edge family with
off-support vertices into a direct support-cluster selector. -/
def RankCertifiedNormalizedUrsellCanonicalAmbientContraction
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] : Prop :=
  Mayer.SupportPartitionCanonicalAmbientToWeightedContractionGeTwo (G := K) (q := q)
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)

/-- Covering-family form of the strongest normalized, rank-certified
resummation leaf.  This is the genuine source-level Mayer/Ursell cancellation
identity after finite ambient reindexing has been removed. -/
def RankCertifiedNormalizedUrsellCoveringContraction
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] : Prop :=
  Mayer.SupportPartitionCoveringWeightedContractionGeTwo (G := K) (q := q)
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)

/-- Fixed-support form of
`RankCertifiedNormalizedUrsellCoveringContraction`.  This is the local
Mayer/Ursell identity that remains after the top-level security theorem has
chosen a concrete ANOVA support. -/
def RankCertifiedNormalizedUrsellCoveringSupportContraction
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q)) : Prop :=
  (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
      (fun Γ => S ⊆ edgeVertices Γ),
    anovaComponent S
      (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
  fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
    Mayer.supportPartitionWeightedClusterProductContribution
      (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
      (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y

/-- Pointwise fixed-support form of the normalized rank-certified covering
contraction. -/
def RankCertifiedNormalizedUrsellCoveringSupportPointwise
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q)) : Prop :=
  ∀ y : Fin q → K,
    (∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
    ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
      Mayer.supportPartitionWeightedClusterProductContribution
        (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
        (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y

/-- Pointwise fixed-support contraction closes the fixed-support function
equality. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportContraction_of_pointwise
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)}
    (hpoint : RankCertifiedNormalizedUrsellCoveringSupportPointwise (q := q) K S) :
    RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S := by
  funext y
  exact hpoint y

/-- The normalized rank-certified support contribution indexed by a support
partition.  This names the RHS block of the covering contraction so that the
correct centered selected-fiber target can be stated without duplicating the
long weighted-product expression. -/
noncomputable def rankCertifiedNormalizedUrsellSupportContribution
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q)) (idx : Mayer.SupportPartitionClusters (q := q) S) :
    (Fin q → K) → ℝ :=
  fun y =>
    Mayer.supportPartitionWeightedClusterProductContribution
      (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
      (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y

/-- Centered fixed-support form of the normalized rank-certified covering
contraction.  This is the shape forced by the ANOVA-centered covering-family
sum: each selected support-partition contribution is projected to its
`S`-component before summing. -/
def RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q)) : Prop :=
  (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
      (fun Γ => S ⊆ edgeVertices Γ),
    anovaComponent S
      (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
  fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
    anovaComponent S
      (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) y

/-- The filtered centered covering-family sum is the actual `S`-ANOVA
component of the XoP density error.  This bridge lets fixed-support contraction
proofs target `anovaComponent S xopError` directly while reusing the existing
off-support vanishing and component-factorization lemmas. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportCentered_lhs_eq_xopError
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
      (fun Γ => S ⊆ edgeVertices Γ),
    anovaComponent S
      (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
      anovaComponent S (xopError (G := K) (q := q)) := by
  classical
  funext y
  let A := (Finset.univ : Finset (PairEdge (coordinates q))).powerset
  let termC := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y
  let termN := fun Γ : Finset (PairEdge (coordinates q)) =>
    anovaComponent S (normalizedPairFamilyTerm (G := K) Γ) y
  have hsum :=
    congrFun (Mayer.anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty
      (G := K) (q := q) hS) y
  calc
    (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), termC Γ)
        = ∑ Γ ∈ A, termN Γ := by
          calc
            (∑ Γ ∈ A.filter (fun Γ => S ⊆ edgeVertices Γ), termC Γ)
                = ∑ Γ ∈ A, if S ⊆ edgeVertices Γ then termC Γ else 0 := by
                    rw [Finset.sum_filter]
            _ = ∑ Γ ∈ A, termN Γ := by
                    refine Finset.sum_congr rfl ?_
                    intro Γ _hΓ
                    by_cases hcover : S ⊆ edgeVertices Γ
                    · simp [hcover, termC, termN,
                        Mayer.normalizedPairFamilyTerm_eq_componentFactorized]
                    · have hzero : termN Γ = 0 := by
                        dsimp [termN]
                        rw [Mayer.anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'
                          (G := K) (q := q) Γ hcover]
                      simp [hcover, hzero]
    _ = anovaComponent S (xopError (G := K) (q := q)) y := by
          simpa [A, termN] using hsum.symm

/-- Fixed-support centered contraction from a direct identity for the
corresponding `S`-ANOVA component of the XoP density error. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportCenteredContraction_of_xopError_anova
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)} (hS : S.Nonempty)
    (hxop : anovaComponent S (xopError (G := K) (q := q)) =
      fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        anovaComponent S
          (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) y) :
    RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S := by
  exact Eq.trans
    (rankCertifiedNormalizedUrsell_coveringSupportCentered_lhs_eq_xopError
      (q := q) (K := K) hS)
    hxop

/-- Named base-pair obligation for the corrected centered normalized-Ursell
route. -/
def RankCertifiedNormalizedUrsellCenteredPairSupportContractions
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.card = 2 →
    RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S

/-- Named lower leaf for the base pair branch: identify the two-support ANOVA
component of the XoP density error with the centered rank-certified
support-partition contribution. -/
def RankCertifiedNormalizedUrsellCenteredPairSupportAnovaIdentities
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.card = 2 →
    anovaComponent S (xopError (G := K) (q := q)) =
      fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        anovaComponent S
          (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) y

/-- The pair-support ANOVA identities close the named base-pair centered
covering contraction obligation. -/
theorem rankCertifiedNormalizedUrsell_centeredPairSupportContractions_of_pairAnovaIdentities
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hxop : RankCertifiedNormalizedUrsellCenteredPairSupportAnovaIdentities (q := q) K) :
    RankCertifiedNormalizedUrsellCenteredPairSupportContractions (q := q) K := by
  intro S hSpow hcard
  have hS : S.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  exact rankCertifiedNormalizedUrsell_coveringSupportCenteredContraction_of_xopError_anova
    (q := q) (K := K) hS (hxop S hSpow hcard)

/-- Hard fixed-support selected-fiber identity with the corrected centered
target.  The uncentered version is too strong for the pair-support base case:
the left side is ANOVA-centered, while the raw full-atom fiber contribution has
nonzero uniform average. -/
def RankCertifiedNormalizedUrsellCenteredSelectedFiberIdentity
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q))
    [DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    (select : Finset (PairEdge (coordinates q)) →
      Mayer.SupportPartitionClusters (q := q) S) : Prop :=
  ∀ idx : Mayer.SupportPartitionClusters (q := q) S,
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
    anovaComponent S
      (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)

/-- Centered selected-fiber identities reassemble to the centered
fixed-support contraction by finite fiber reindexing. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportCenteredContraction_of_centeredSelectedFiberIdentity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)}
    [DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {select : Finset (PairEdge (coordinates q)) →
      Mayer.SupportPartitionClusters (q := q) S}
    (hfiber : RankCertifiedNormalizedUrsellCenteredSelectedFiberIdentity (q := q) K S select) :
    RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S := by
  exact Mayer.supportPartitionCoveringSupportContraction_of_selected_fibers
    (G := K) (q := q) S
    (fun idx => anovaComponent S
      (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx))
    select (by
      simpa [RankCertifiedNormalizedUrsellCenteredSelectedFiberIdentity] using hfiber)

/-- A centered selected-fiber identity closes the original uncentered
fixed-support contraction only after proving that the summed rank-certified
support contribution is already equal to its `S`-ANOVA projection.  This lemma
exposes the exact remaining centering obligation instead of hiding it in the
selected-fiber target. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportContraction_of_centeredSelectedFiberIdentity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)}
    [DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {select : Finset (PairEdge (coordinates q)) →
      Mayer.SupportPartitionClusters (q := q) S}
    (hfiber : RankCertifiedNormalizedUrsellCenteredSelectedFiberIdentity (q := q) K S select)
    (hcenter : (fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
      anovaComponent S
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) y) =
      fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx y) :
    RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S := by
  exact Eq.trans
    (rankCertifiedNormalizedUrsell_coveringSupportCenteredContraction_of_centeredSelectedFiberIdentity
      (q := q) (K := K) hfiber)
    hcenter

/-- Global covering contraction with centered support-partition contributions.
This is the corrected support-indexed expansion leaf after the selected-fiber
identity has been centered on both sides. -/
def RankCertifiedNormalizedUrsellCenteredCoveringContraction
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S

/-- Fixed-support centered contractions for every theorem-relevant support
close the global centered covering contraction. -/
theorem rankCertifiedNormalizedUrsell_centeredCoveringContraction_of_supportContractions
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hsupport : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S) :
    RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K := by
  intro S hSpow hS hge
  exact hsupport S hSpow hS hge

/-- The centered fixed-support covering contraction splits into the base pair
interaction and the genuine higher-order support case. -/
theorem rankCertifiedNormalizedUrsell_centeredCoveringContraction_of_pair_and_ge_three
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hpair : ∀ S ∈ (coordinates q).powerset, S.card = 2 →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hlarge : ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S) :
    RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K := by
  refine rankCertifiedNormalizedUrsell_centeredCoveringContraction_of_supportContractions
    (q := q) (K := K) ?_
  intro S hSpow _hS hge
  by_cases hcard : S.card = 2
  · exact hpair S hSpow hcard
  · exact hlarge S hSpow (by omega)

/-- The centered covering contraction is exactly the expansion interface needed
by the generic support-indexed activity endpoint. -/
theorem rankCertifiedNormalizedUrsell_supportIndexedExpansion_of_centeredCoveringContraction
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K) :
    Mayer.SupportIndexedExpansionGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (fun S idx => anovaComponent S
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)) := by
  exact Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedCoveringContraction
    (G := K) (q := q)
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
    hcovering

set_option maxHeartbeats 800000 in
/-- Corrected normalized-Ursell endpoint using centered support-partition
contributions.  This is the theorem-facing replacement for routes that tried
to identify an ANOVA-centered covering sum with uncentered rank-certified
support products.  The activity premise is stated directly on the centered
contributions, so later rank/atomization work may pay an ANOVA projection
factor explicitly. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_activity_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hactivityBound : Mayer.SupportIndexedActivityBoundGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (fun S idx => anovaComponent S
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx))
      localActivity)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact Mayer.xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_card_scaled_quadratic
    (G := K) (q := q)
    (Index := Mayer.SupportPartitionClusters (q := q))
    (contribution := fun S idx => anovaComponent S
      (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx))
    (localActivity := localActivity) (C := Cconst)
    hq
    (rankCertifiedNormalizedUrsell_supportIndexedExpansion_of_centeredCoveringContraction
      (q := q) (K := K) hcovering)
    hactivityBound hC hsmall hactivity

/-- Centered activity from raw support-partition activity, paying the standard
ANOVA projection factor `|powerset S|`.  This is the reusable bridge from the
existing uncentered rank/atomized budget machinery into the corrected centered
support-indexed endpoint. -/
theorem rankCertifiedNormalizedUrsell_centeredActivityBound_of_rawActivity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {rawActivity localActivity : Nat → ℝ}
    (hraw : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        visibleL1 (G := K) (q := q)
          (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)) ≤
        rawActivity S.card)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card) :
    Mayer.SupportIndexedActivityBoundGeTwo (G := K) (q := q)
      (Mayer.SupportPartitionClusters (q := q))
      (fun S idx => anovaComponent S
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx))
      localActivity := by
  intro S hSpow hS hge
  calc
    (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        visibleL1 (G := K) (q := q)
          (anovaComponent S
            (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)))
        ≤ ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
            (S.powerset.card : ℝ) *
              visibleL1 (G := K) (q := q)
                (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) := by
          refine Finset.sum_le_sum ?_
          intro idx _hidx
          exact RandomSystems.Applications.XoP.ANOVA.visibleL1_anovaComponent_le_card_powerset_mul_visibleL1
            (G := K) (q := q) S
            (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)
    _ = (S.powerset.card : ℝ) *
          ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
            visibleL1 (G := K) (q := q)
              (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) := by
          rw [Finset.mul_sum]
    _ ≤ (S.powerset.card : ℝ) * rawActivity S.card := by
          exact mul_le_mul_of_nonneg_left (hraw S hSpow hS hge) (Nat.cast_nonneg _)
    _ ≤ localActivity S.card := hcenter S hSpow hS hge

set_option maxHeartbeats 800000 in
/-- Corrected centered-covering endpoint with the activity premise reduced to
raw uncentered support-contribution activity plus the explicit ANOVA projection
factor.  This is the next theorem-facing target for the rank/atomization scalar
budget after the centering correction. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_rawActivity_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {rawActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hraw : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        visibleL1 (G := K) (q := q)
          (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)) ≤
        rawActivity S.card)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_activity_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hcovering
    (rankCertifiedNormalizedUrsell_centeredActivityBound_of_rawActivity
      (q := q) (K := K) (rawActivity := rawActivity) (localActivity := localActivity)
      hraw hcenter)
    hC hsmall hactivity

/-- Fixed-support selector/fiber bridge specialized to the normalized
rank-certified covering contraction. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportContraction_of_selected_fibers
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)}
    [DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    (select : Finset (PairEdge (coordinates q)) →
      Mayer.SupportPartitionClusters (q := q) S)
    (hfiber : ∀ idx : Mayer.SupportPartitionClusters (q := q) S,
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
          (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
      fun y =>
        Mayer.supportPartitionWeightedClusterProductContribution
          (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
          (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y) :
    RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S := by
  exact Mayer.supportPartitionCoveringWeightedSupportContraction_of_selected_fibers
    (G := K) (q := q) S
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
    select hfiber

/-- Hard fixed-support selected-fiber identity for the normalized
rank-certified covering contraction.  The selector itself is supplied by the
branch under consideration; this Prop names the precise fiberwise equality that
must be proved next. -/
def RankCertifiedNormalizedUrsellSelectedFiberIdentity
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q))
    [DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    (select : Finset (PairEdge (coordinates q)) →
      Mayer.SupportPartitionClusters (q := q) S) : Prop :=
  ∀ idx : Mayer.SupportPartitionClusters (q := q) S,
    (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
        (fun Γ => S ⊆ edgeVertices Γ ∧ select Γ = idx),
      anovaComponent S
        (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
    fun y =>
      Mayer.supportPartitionWeightedClusterProductContribution
        (G := K) (q := q) (supportPartitionNormalizedUrsellWeight (q := q) K)
        (rankCertifiedSignedPairMayerBlockContribution (q := q) K) S idx y

/-- Named selected-fiber form of the fixed-support contraction. -/
theorem rankCertifiedNormalizedUrsell_coveringSupportContraction_of_selectedFiberIdentity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {S : Finset (Fin q)}
    [DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {select : Finset (PairEdge (coordinates q)) →
      Mayer.SupportPartitionClusters (q := q) S}
    (hfiber : RankCertifiedNormalizedUrsellSelectedFiberIdentity (q := q) K S select) :
    RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S := by
  exact rankCertifiedNormalizedUrsell_coveringSupportContraction_of_selected_fibers
    (q := q) (K := K) select (by
      simpa [RankCertifiedNormalizedUrsellSelectedFiberIdentity] using hfiber)

/-- Fixed-support contractions for every theorem-relevant support close the
global covering contraction. -/
theorem rankCertifiedNormalizedUrsell_coveringContraction_of_supportContractions
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hsupport : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S) :
    RankCertifiedNormalizedUrsellCoveringContraction (q := q) K := by
  intro S hSpow hS hge
  exact hsupport S hSpow hS hge

/-- The fixed-support covering contraction splits into the base pair
interaction and the genuine higher-order support case. -/
theorem rankCertifiedNormalizedUrsell_coveringContraction_of_pair_and_ge_three
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hpair : ∀ S ∈ (coordinates q).powerset, S.card = 2 →
      RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S)
    (hlarge : ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportContraction (q := q) K S) :
    RankCertifiedNormalizedUrsellCoveringContraction (q := q) K := by
  refine rankCertifiedNormalizedUrsell_coveringContraction_of_supportContractions
    (q := q) (K := K) ?_
  intro S hSpow _hS hge
  by_cases hcard : S.card = 2
  · exact hpair S hSpow hcard
  · exact hlarge S hSpow (by omega)

/-- The covering-family normalized/rank-certified contraction supplies the
canonical ambient contraction consumed by the current strongest endpoint. -/
theorem rankCertifiedNormalizedUrsell_canonicalAmbientContraction_of_coveringContraction
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hcovering : RankCertifiedNormalizedUrsellCoveringContraction (q := q) K) :
    RankCertifiedNormalizedUrsellCanonicalAmbientContraction (q := q) K := by
  exact Mayer.supportPartitionCanonicalAmbientToWeightedContractionGeTwo_of_coveringWeighted
    (G := K) (q := q)
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
    hcovering

/-- The source-faithful canonical ambient contraction supplies the weighted
resummation premise consumed by the normalized rank-certified endpoint. -/
theorem rankCertifiedNormalizedUrsell_weightedResummation_of_canonicalAmbientContraction
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hcontract : RankCertifiedNormalizedUrsellCanonicalAmbientContraction (q := q) K) :
    Mayer.SupportPartitionWeightedResummationGeTwo (G := K) (q := q)
      (supportPartitionNormalizedUrsellWeight (q := q) K)
      (rankCertifiedSignedPairMayerBlockContribution (q := q) K) := by
  exact Mayer.supportPartitionWeightedResummationGeTwo_of_ambientFiber_weightedContraction
    (G := K) (q := q)
    (Mayer.supportPartitionCanonicalAmbientFiberContribution (G := K) (q := q))
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
    (Mayer.supportPartitionCanonicalAmbientFiberResummationGeTwo (G := K) (q := q))
    hcontract

/-- Corrected normalized-Ursell endpoint from block-local certified signed
atomized evaluations.  The remaining hard `hresum` premise is the genuine
ANOVA/Ursell cancellation statement; the rank side only sees block-local terms
that already carry vertex, connectivity, and visible-obstruction certificates. -/
theorem xop_advantageOn_injective_of_normalizedUrsell_blockLocalSignedAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (BlockTerm : {S : Finset (Fin q)} → PairCluster S → Type*)
    [blockTermFintype : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      Fintype (BlockTerm C)]
    (blockCoeff : ∀ {S : Finset (Fin q)} (C : PairCluster S), BlockTerm C → ℝ)
    (blockAtoms : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      BlockTerm C → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionWeightedResummationGeTwo (G := K) (q := q)
      (supportPartitionNormalizedUrsellWeight (q := q) K) blockContribution)
    (hblockEval : ∀ {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → K),
      blockContribution S C y =
        ∑ tB : BlockTerm C,
          blockCoeff C tB *
            (Fintype.card {aS : S → K //
              AtomFamilyHoldsOn (q := q) y (blockAtoms C tB) aS} : ℝ))
    (hblocks : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S)
      (t : (B : i.1.parts) → BlockTerm (i.2 B)) (B : i.1.parts),
      atomVertices (blockAtoms (i.2 B) (t B)) = B.1)
    (hconn : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S)
      (t : (B : i.1.parts) → BlockTerm (i.2 B)) (B : i.1.parts), ∃ r,
        r ∈ atomVertices (blockAtoms (i.2 B) (t B)) ∧
        ∀ j ∈ atomVertices (blockAtoms (i.2 B) (t B)),
          Relation.ReflTransGen (atomLinked (blockAtoms (i.2 B) (t B))) r j)
    (hvis : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S)
      (t : (B : i.1.parts) → BlockTerm (i.2 B)) (B : i.1.parts),
        HasVisibleObstruction (q := q) K (atomFamilyRow (blockAtoms (i.2 B) (t B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ ((B : i.1.parts) → BlockTerm (i.2 B))
            (by infer_instance)),
          |supportPartitionNormalizedUrsellWeight (q := q) K S i *
              ((∏ B : i.1.parts, blockCoeff (i.2 B) (t B)) /
                (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_weightedResummation_blockLocalSignedAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (supportPartitionNormalizedUrsellWeight (q := q) K) blockContribution
    BlockTerm blockCoeff blockAtoms hq hresum hblockEval hblocks hconn hvis
    hbudget hC hsmall hactivity

/-- The theorem-facing certified normalized-Ursell branch.  The two remaining
mathematical premises are exactly the certified resummation theorem and the
factorial-paid scalar activity budget for certified block choices. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionWeightedResummationGeTwo (G := K) (q := q)
      (supportPartitionNormalizedUrsellWeight (q := q) K)
      (rankCertifiedSignedPairMayerBlockContribution (q := q) K))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ ((B : i.1.parts) →
            RankCertifiedPairAtomChoiceFamily (q := q) K
              (Mayer.pairClusterSupportEdges (i.2 B))) (by infer_instance)),
          |supportPartitionNormalizedUrsellWeight (q := q) K S i *
              ((∏ B : i.1.parts,
                  rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K (t B)) /
                (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_normalizedUrsell_blockLocalSignedAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
    (fun {S : Finset (Fin q)} (C : PairCluster S) =>
      RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C))
    (fun {_S : Finset (Fin q)} _C t =>
      rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t)
    (fun {_S : Finset (Fin q)} _C t =>
      rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t)
    hq hresum
    (by
      intro S C y
      exact rankCertifiedSignedPairMayerBlockContribution_blockLocalEval
        (K := K) (q := q) C y)
    (by
      intro S i t B
      exact atomVertices_rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges
        (K := K) (q := q) (i.2 B) (t B))
    (by
      intro S i t B
      exact rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges_connected
        (K := K) (q := q) (i.2 B)
        (Mayer.supportPartitionClusters_block_nonempty (q := q) i B) (t B))
    (by
      intro S i t B
      exact rankCertifiedPairAtomChoiceFamily_hasVisibleObstruction
        (K := K) (q := q) (t B))
    hbudget hC hsmall hactivity

/-- Certified normalized-Ursell endpoint from a covering-fiber resummation
obligation.  This is the next theorem-shaped child below the certified
resummation premise: the remaining cancellation must now be proved fiberwise
for a concrete selector. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ ((B : i.1.parts) →
            RankCertifiedPairAtomChoiceFamily (q := q) K
              (Mayer.pairClusterSupportEdges (i.2 B))) (by infer_instance)),
          |supportPartitionNormalizedUrsellWeight (q := q) K S i *
              ((∏ B : i.1.parts,
                  rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K (t B)) /
                (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq ?_ hbudget hC hsmall hactivity
  exact Mayer.supportPartitionWeightedResummationGeTwo_of_exists_coveringFiber_resummation
    (G := K) (q := q)
    (supportPartitionNormalizedUrsellWeight (q := q) K)
    (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
    hselect

/-- Certified block-choice assignments for a support-partition index.  Naming
this dependent function type keeps scalar-budget endpoints cheap to elaborate. -/
def rankCertifiedBlockChoiceAssignments (K : Type*) [Field K]
    {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S) : Type _ :=
  (B : i.1.parts) →
    RankCertifiedPairAtomChoiceFamily (q := q) K
      (Mayer.pairClusterSupportEdges (i.2 B))

instance rankCertifiedBlockChoiceAssignmentsFintype (K : Type*) [Field K]
    {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S) :
    Fintype (rankCertifiedBlockChoiceAssignments (q := q) K i) := by
  dsimp [rankCertifiedBlockChoiceAssignments]
  infer_instance

/-- Product form of the certified block-choice assignment count.  This is the
form produced by summing the independent block choices. -/
def rankCertifiedBlockChoiceAssignmentsCard (K : Type*) [Field K]
    {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S) : ℝ :=
  ∏ B : i.1.parts,
    (Fintype.card (RankCertifiedPairAtomChoiceFamily (q := q) K
      (Mayer.pairClusterSupportEdges (i.2 B))) : ℝ)

/-- The certified block-choice product is bounded by the raw three-choice
product over the block support edges. -/
theorem rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_edges
    (K : Type*) [Field K] {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) :
    rankCertifiedBlockChoiceAssignmentsCard (q := q) K i ≤
      ∏ B : i.1.parts,
        ((3 : ℝ) ^ (Mayer.pairClusterSupportEdges (i.2 B)).card) := by
  classical
  unfold rankCertifiedBlockChoiceAssignmentsCard
  refine Finset.prod_le_prod ?nonneg ?le
  · intro B _hB
    exact Nat.cast_nonneg _
  · intro B _hB
    exact_mod_cast card_rankCertifiedPairAtomChoiceFamily_le_three_pow (q := q) K
      (Mayer.pairClusterSupportEdges (i.2 B))

/-- Product form of the preceding raw three-choice bound. -/
theorem prod_three_pow_pairClusterSupportEdges_card
    {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S) :
    (∏ B : i.1.parts,
        ((3 : ℝ) ^ (Mayer.pairClusterSupportEdges (i.2 B)).card)) =
      (3 : ℝ) ^ (∑ B : i.1.parts, (Mayer.pairClusterSupportEdges (i.2 B)).card) := by
  exact Finset.prod_pow_eq_pow_sum Finset.univ
    (fun B : i.1.parts => (Mayer.pairClusterSupportEdges (i.2 B)).card) (3 : ℝ)

/-- Single-exponent form of the certified block-choice count. -/
theorem rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_sum_supportEdges
    (K : Type*) [Field K] {S : Finset (Fin q)}
    (i : Mayer.SupportPartitionClusters (q := q) S) :
    rankCertifiedBlockChoiceAssignmentsCard (q := q) K i ≤
      (3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card) := by
  calc
    rankCertifiedBlockChoiceAssignmentsCard (q := q) K i ≤
      ∏ B : i.1.parts,
        ((3 : ℝ) ^ (Mayer.pairClusterSupportEdges (i.2 B)).card) :=
        rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_edges (q := q) K i
    _ = (3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card) :=
        prod_three_pow_pairClusterSupportEdges_card (q := q) i

/-- Counted scalar budget contribution for one certified normalized-Ursell
support-partition index. -/
def rankCertifiedNormalizedUrsellIndexCardBudget
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (S : Finset (Fin q)) (i : Mayer.SupportPartitionClusters (q := q) S) : ℝ :=
  rankCertifiedBlockChoiceAssignmentsCard (q := q) K i *
    (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
        (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
      ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
        (Fintype.card K : ℝ) ^ q))

/-- Raw support activity from per-index rank-certified budgets.  This is the
summation bridge below the centered endpoint; the remaining hard leaf is the
single-index estimate from the concrete rank-certified support contribution to
`rankCertifiedNormalizedUrsellIndexCardBudget`. -/
theorem rankCertifiedNormalizedUrsell_rawActivityBound_of_indexCardBudget
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {rawActivity : Nat → ℝ}
    (hindex : ∀ S (idx : Mayer.SupportPartitionClusters (q := q) S),
      visibleL1 (G := K) (q := q)
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) ≤
      rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx) ≤
        rawActivity S.card) :
    ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        visibleL1 (G := K) (q := q)
          (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)) ≤
        rawActivity S.card := by
  intro S hSpow hS hge
  calc
    (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        visibleL1 (G := K) (q := q)
          (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx))
        ≤ ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
            rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx := by
          exact Finset.sum_le_sum (fun idx _hidx => hindex S idx)
    _ ≤ rawActivity S.card := hbudget S hSpow hS hge

/-- Single-index raw `L¹` estimate for the normalized rank-certified support
contribution.  This discharges the local leaf exposed by
`rankCertifiedNormalizedUrsell_rawActivityBound_of_indexCardBudget`. -/
theorem rankCertifiedNormalizedUrsellSupportContribution_visibleL1_le_indexCardBudget
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (S : Finset (Fin q)) (idx : Mayer.SupportPartitionClusters (q := q) S) :
    visibleL1 (G := K) (q := q)
      (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) ≤
    rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx := by
  classical
  let Term := rankCertifiedBlockChoiceAssignments (q := q) K idx
  let coeff : Term → ℝ := fun t =>
    supportPartitionNormalizedUrsellWeight (q := q) K S idx *
      ((∏ B : idx.1.parts,
          rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K (t B)) /
        (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))
  let atoms : Term → Finset (Atom S) := fun t =>
    supportPartitionAtomFamily idx.1
      (fun B : idx.1.parts =>
        rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K (t B))
  have heval :
      rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx =
        fun y : Fin q → K =>
          ∑ t : Term,
            coeff t *
              (Fintype.card {a : Fin q → K // AtomFamilyHolds y a (atoms t)} : ℝ) := by
    funext y
    dsimp [rankCertifiedNormalizedUrsellSupportContribution]
    rw [Mayer.supportPartitionWeightedClusterProductContribution]
    have hunweighted :=
      supportPartitionClusterProductContribution_eq_sum_pi_blockLocalAtomized
        (q := q) (K := K)
        (rankCertifiedSignedPairMayerBlockContribution (q := q) K)
        (fun {S : Finset (Fin q)} (C : PairCluster S) =>
          RankCertifiedPairAtomChoiceFamily (q := q) K (Mayer.pairClusterSupportEdges C))
        (fun {_S : Finset (Fin q)} _C t =>
          rankCertifiedPairAtomChoiceFamilyCoeff (q := q) K t)
        (fun {_S : Finset (Fin q)} _C t =>
          rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K t)
        (by
          intro S C y
          exact rankCertifiedSignedPairMayerBlockContribution_blockLocalEval
            (K := K) (q := q) C y)
        idx y
    rw [hunweighted]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    dsimp [Term, coeff, atoms, rankCertifiedBlockChoiceAssignments]
    ring
  have hvr : ∀ t : Term, S.card ≤ jointRank (q := q) K (atomFamilyRow (atoms t)) := by
    intro t
    dsimp [Term, atoms, rankCertifiedBlockChoiceAssignments]
    exact jointRank_ge_card_of_supportPartitionClusterBlockAtoms (q := q) (K := K)
      idx
      (supportPartitionAtomFamily idx.1
        (fun B : idx.1.parts =>
          rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K (t B)))
      (fun B : idx.1.parts =>
        rankCertifiedPairAtomChoiceFamilyAtoms (q := q) K (t B))
      rfl
      (fun B : idx.1.parts =>
        atomVertices_rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges
          (K := K) (q := q) (idx.2 B) (t B))
      (fun B : idx.1.parts =>
        rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges_connected
          (K := K) (q := q) (idx.2 B)
          (Mayer.supportPartitionClusters_block_nonempty (q := q) idx B) (t B))
      (fun B : idx.1.parts =>
        rankCertifiedPairAtomChoiceFamily_hasVisibleObstruction
          (K := K) (q := q) (t B))
  have hraw :=
    visibleL1_atomized_eval_le_sum_jointRankBudget
      (q := q) (K := K) (S := S)
      (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx)
      coeff atoms (fun _ : Term => S.card) heval hvr
  have hcardTerm :
      (Fintype.card Term : ℝ) =
        rankCertifiedBlockChoiceAssignmentsCard (q := q) K idx := by
    dsimp [Term, rankCertifiedBlockChoiceAssignments, rankCertifiedBlockChoiceAssignmentsCard]
    exact_mod_cast (Fintype.card_pi :
      Fintype.card ((B : idx.1.parts) →
        RankCertifiedPairAtomChoiceFamily (q := q) K
          (Mayer.pairClusterSupportEdges (idx.2 B))) =
        ∏ B : idx.1.parts,
          Fintype.card (RankCertifiedPairAtomChoiceFamily (q := q) K
            (Mayer.pairClusterSupportEdges (idx.2 B))))
  refine le_trans hraw ?_
  dsimp [coeff]
  simp [rankCertifiedNormalizedUrsellIndexCardBudget,
    hcardTerm, abs_mul, Finset.abs_prod,
    abs_rankCertifiedPairAtomChoiceFamilyCoeff, Finset.prod_const,
    div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

set_option maxHeartbeats 800000 in
/-- Corrected centered-covering endpoint with raw activity supplied by the
rank-certified index-card budget.  The remaining local proof obligation is the
single-index estimate
`visibleL1 rankCertifiedNormalizedUrsellSupportContribution ≤
rankCertifiedNormalizedUrsellIndexCardBudget`. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_indexCardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {rawActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hindex : ∀ S (idx : Mayer.SupportPartitionClusters (q := q) S),
      visibleL1 (G := K) (q := q)
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) ≤
      rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx) ≤
        rawActivity S.card)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_rawActivity_quadratic
    (K := K) (q := q) (rawActivity := rawActivity) (localActivity := localActivity)
    (Cconst := Cconst) hq hcovering
    (rankCertifiedNormalizedUrsell_rawActivityBound_of_indexCardBudget
      (q := q) (K := K) (rawActivity := rawActivity) hindex hbudget)
    hcenter hC hsmall hactivity

set_option maxHeartbeats 800000 in
/-- Corrected centered-covering endpoint after discharging the local
single-index rank-certified atomization estimate.  The remaining premise is
now purely scalar: the summed index-card budget must be bounded by the chosen
raw activity sequence. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_indexBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {rawActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S idx) ≤
        rawActivity S.card)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_indexCardBudget_quadratic
    (K := K) (q := q) (rawActivity := rawActivity) (localActivity := localActivity)
    (Cconst := Cconst) hq hcovering
    (rankCertifiedNormalizedUrsellSupportContribution_visibleL1_le_indexCardBudget
      (q := q) (K := K))
    hbudget hcenter hC hsmall hactivity

/-- One-index counted budget with the certified-choice count replaced by the
raw three-choice product.  This is the first scalar comparison needed before
using Penrose/tree estimates for the remaining support-partition weights. -/
theorem rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_edges
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S) :
    rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i ≤
      (∏ B : i.1.parts,
        ((3 : ℝ) ^ (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
      (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
          (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
        ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
          (Fintype.card K : ℝ) ^ q)) := by
  classical
  unfold rankCertifiedNormalizedUrsellIndexCardBudget
  refine mul_le_mul_of_nonneg_right
    (rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_edges (q := q) K i) ?_
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))

/-- One-index counted budget with the certified-choice count replaced by a
single `3^(sum edge counts)` factor. -/
theorem rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_sum_supportEdges
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S) :
    rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i ≤
      ((3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
      (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
          (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
        ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
          (Fintype.card K : ℝ) ^ q)) := by
  classical
  unfold rankCertifiedNormalizedUrsellIndexCardBudget
  refine mul_le_mul_of_nonneg_right
    (rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_sum_supportEdges (q := q) K i) ?_
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))

/-- One-index counted budget after cancelling the outside-support normalizer and
bounding the Ursell coefficient by `S.card!`. -/
theorem rankCertifiedNormalizedUrsellIndexCardBudget_le_factorial_three_pow_edges
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    (hq : q ≤ Fintype.card K)
    {S : Finset (Fin q)} (hSpow : S ∈ (coordinates q).powerset)
    (i : Mayer.SupportPartitionClusters (q := q) S) :
    rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i ≤
      ((3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
      ((Nat.factorial S.card : ℝ) *
        (((Fintype.card K : ℝ) ^ q /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
          (Fintype.card K : ℝ) ^ S.card)) := by
  classical
  calc
    rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i ≤
      ((3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
      (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
          (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
        ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
          (Fintype.card K : ℝ) ^ q)) :=
        rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_sum_supportEdges
          (q := q) (K := K) i
    _ ≤ ((3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
      ((Nat.factorial S.card : ℝ) *
        (((Fintype.card K : ℝ) ^ q /
          (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
          (Fintype.card K : ℝ) ^ S.card)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        let N : ℝ := Fintype.card K
        let Z : ℝ := (visibleNormalizerNNReal (G := K) (q := q) : ℝ)
        let Cc : ℝ := Fintype.card ({j : Fin q // j ∉ S} → K)
        have hSsub : S ⊆ coordinates q := by simpa using hSpow
        have hv_le : S.card ≤ q := by
          simpa [coordinates] using Finset.card_le_card hSsub
        have hN_pos : 0 < N := by
          dsimp [N]
          exact_mod_cast Fintype.card_pos (α := K)
        have hN_ne : N ≠ 0 := ne_of_gt hN_pos
        have hZ_pos : 0 < Z := by
          dsimp [Z]
          rw [NNReal.coe_pos]
          exact lt_of_le_of_ne bot_le
            (Ne.symm (visibleNormalizerNNReal_ne_zero (G := K) (q := q) hq))
        have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
        have hCc_pos : 0 < Cc := by
          dsimp [Cc]
          exact_mod_cast Fintype.card_pos (α := ({j : Fin q // j ∉ S} → K))
        have hCc_ne : Cc ≠ 0 := ne_of_gt hCc_pos
        have hCc_abs : |Cc / Z * (1 / Cc)| = 1 / Z := by
          have hmul : Cc / Z * (1 / Cc) = 1 / Z := by
            field_simp [hCc_ne, hZ_ne]
          rw [hmul, abs_of_pos (one_div_pos.mpr hZ_pos)]
        have hnorm_abs :
            |supportPartitionNormalizedUrsellWeight (q := q) K S i * (1 / Cc)| =
              |Mayer.supportPartitionUrsellWeight (q := q) S i| * (1 / Z) := by
          let U : ℝ := Mayer.supportPartitionUrsellWeight (q := q) S i
          have hmul : (U * (Cc / Z)) * (1 / Cc) = U * (1 / Z) := by
            field_simp [hCc_ne, hZ_ne]
          simp only [supportPartitionNormalizedUrsellWeight]
          rw [show (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) = Cc by rfl]
          change |(U * (Cc / Z)) * (1 / Cc)| = |U| * (1 / Z)
          rw [hmul, abs_mul, abs_of_pos (one_div_pos.mpr hZ_pos)]
        have hursell_le :
            |Mayer.supportPartitionUrsellWeight (q := q) S i| ≤
              (Nat.factorial S.card : ℝ) :=
          Mayer.abs_supportPartitionUrsellWeight_le_factorial_card (q := q) S i
        have hpow_simpl :
            N ^ (2 * q - S.card) / N ^ q = N ^ q / N ^ S.card := by
          have htwice : 2 * q - S.card = q + (q - S.card) := by omega
          have hden : N ^ q = N ^ (q - S.card) * N ^ S.card := by
            rw [← pow_add, Nat.sub_add_cancel hv_le]
          rw [htwice, pow_add, hden]
          field_simp [hN_ne]
        have htarget_eq :
            (Nat.factorial S.card : ℝ) * ((N ^ q / Z) / N ^ S.card) =
              (Nat.factorial S.card : ℝ) * (1 / Z) * (N ^ (2 * q - S.card) / N ^ q) := by
          rw [hpow_simpl]
          field_simp [hN_ne, hZ_ne]
        rw [show (Fintype.card K : ℝ) = N by rfl]
        rw [show (visibleNormalizerNNReal (G := K) (q := q) : ℝ) = Z by rfl]
        rw [show (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ) = Cc by rfl]
        rw [hnorm_abs, htarget_eq]
        have hpowratio_nonneg : 0 ≤ N ^ (2 * q - S.card) / N ^ q :=
          div_nonneg (pow_nonneg (le_of_lt hN_pos) _) (pow_nonneg (le_of_lt hN_pos) _)
        have hscale_nonneg : 0 ≤ (1 / Z) * (N ^ (2 * q - S.card) / N ^ q) :=
          mul_nonneg (le_of_lt (one_div_pos.mpr hZ_pos)) hpowratio_nonneg
        calc
          |Mayer.supportPartitionUrsellWeight (q := q) S i| * (1 / Z) *
              (N ^ (2 * q - S.card) / N ^ q)
              = |Mayer.supportPartitionUrsellWeight (q := q) S i| *
                ((1 / Z) * (N ^ (2 * q - S.card) / N ^ q)) := by ring
          _ ≤ (Nat.factorial S.card : ℝ) *
                ((1 / Z) * (N ^ (2 * q - S.card) / N ^ q)) :=
            mul_le_mul_of_nonneg_right hursell_le hscale_nonneg
          _ = (Nat.factorial S.card : ℝ) * (1 / Z) *
                (N ^ (2 * q - S.card) / N ^ q) := by ring

set_option maxHeartbeats 800000 in
/-- Certified normalized-Ursell endpoint with the signed coefficient product
simplified away.  The scalar budget now counts certified block-choice
assignments and the normalized support-partition weight. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_indexCardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i) ≤
          localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hselect ?_ hC hsmall hactivity
  intro S hSpow hS hge
  simpa [rankCertifiedNormalizedUrsellIndexCardBudget,
    rankCertifiedBlockChoiceAssignmentsCard, Finset.sum_const, nsmul_eq_mul,
    Finset.abs_prod, abs_mul, abs_div, div_eq_mul_inv, Finset.prod_const,
    Fintype.card_pi] using
    hbudget S hSpow hS hge

set_option maxHeartbeats 800000 in
/-- Certified normalized-Ursell endpoint whose scalar premise no longer
mentions certified subtypes.  The remaining budget is a pure support-partition
sum with one raw `3^edge-count` factor per block. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_threePowEdgeBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (∏ B : i.1.parts,
          ((3 : ℝ) ^ (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
            (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
          ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
            (Fintype.card K : ℝ) ^ q))) ≤
          localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_indexCardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hselect ?_ hC hsmall hactivity
  intro S hSpow hS hge
  calc
    (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i)
        ≤ ∑ i : Mayer.SupportPartitionClusters (q := q) S,
          (∏ B : i.1.parts,
            ((3 : ℝ) ^ (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
          (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
              (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) := by
          exact Finset.sum_le_sum (fun i _ =>
            rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_edges (q := q) (K := K) i)
    _ ≤ localActivity S.card := hbudget S hSpow hS hge

set_option maxHeartbeats 800000 in
/-- Certified normalized-Ursell endpoint whose scalar premise uses the
single-exponent support-edge count.  This is the scalar interface expected from
the Penrose/tree-fiber estimate. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_threePowSumEdgeBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
            (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
          ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
            (Fintype.card K : ℝ) ^ q))) ≤
          localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_indexCardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hselect ?_ hC hsmall hactivity
  intro S hSpow hS hge
  calc
    (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i)
        ≤ ∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ((3 : ℝ) ^ (∑ B : i.1.parts,
            (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
          (|supportPartitionNormalizedUrsellWeight (q := q) K S i *
              (1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) := by
          exact Finset.sum_le_sum (fun i _ =>
            rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_sum_supportEdges
              (q := q) (K := K) i)
    _ ≤ localActivity S.card := hbudget S hSpow hS hge

/-- Package the factorial/normalizer scalar estimate into the exact
`indexCardBudget` premise required by the certified normalized-Ursell endpoint. -/
theorem rankCertifiedNormalizedUrsell_sum_indexCardBudget_le_of_factorial_three_pow_edges
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card K)
    (hscalar : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        ((Nat.factorial S.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
            (Fintype.card K : ℝ) ^ S.card))) ≤ localActivity S.card) :
    ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i) ≤
          localActivity S.card := by
  intro S hSpow hS hge
  calc
    (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i) ≤
      ∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        ((Nat.factorial S.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
            (Fintype.card K : ℝ) ^ S.card)) := by
        exact Finset.sum_le_sum (fun i _ =>
          rankCertifiedNormalizedUrsellIndexCardBudget_le_factorial_three_pow_edges
            (q := q) (K := K) hq hSpow i)
    _ ≤ localActivity S.card := hscalar S hSpow hS hge

set_option maxHeartbeats 800000 in
/-- Certified normalized-Ursell endpoint with the scalar side reduced to a
factorial/normalizer support-partition estimate. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_factorialThreePowEdgeBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hscalar : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        ((Nat.factorial S.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
            (Fintype.card K : ℝ) ^ S.card))) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_indexCardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hselect ?_ hC hsmall hactivity
  exact rankCertifiedNormalizedUrsell_sum_indexCardBudget_le_of_factorial_three_pow_edges
    (q := q) (K := K) (localActivity := localActivity) hq hscalar

set_option maxHeartbeats 800000 in
/-- Centered-covering endpoint with the scalar side reduced to a
factorial/normalizer support-partition estimate.  Compared with the older
covering-fiber endpoint, this theorem keeps the corrected centered contraction
and pays the explicit ANOVA projection factor through `hcenter`. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_factorialThreePowEdgeBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {rawActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hscalar : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        ((Nat.factorial S.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
            (Fintype.card K : ℝ) ^ S.card))) ≤ rawActivity S.card)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_indexBudget_quadratic
    (K := K) (q := q) (rawActivity := rawActivity) (localActivity := localActivity)
    (Cconst := Cconst) hq hcovering ?_ hcenter hC hsmall hactivity
  exact rankCertifiedNormalizedUrsell_sum_indexCardBudget_le_of_factorial_three_pow_edges
    (q := q) (K := K) (localActivity := rawActivity) hq hscalar

/-- Scalar adapter for the remaining factorial/normalizer support-partition
budget.  It separates the open estimate into a normalizer-slack bound and a
pure support-partition edge-count summability bound. -/
theorem rankCertifiedNormalizedUrsell_hscalar_of_partitionEdgeSummability
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cnorm : ℝ}
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hslack : visibleNormalizerSlackReal K q ≤ Cnorm)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
        (Nat.factorial k : ℝ) * partitionActivity k *
        (Cnorm / (Fintype.card K : ℝ) ^ k) ≤ localActivity k) :
    ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        ((Nat.factorial S.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
            (Fintype.card K : ℝ) ^ S.card))) ≤ localActivity S.card := by
  intro S hSpow hS hge
  let N : ℝ := Fintype.card K
  let slack : ℝ := visibleNormalizerSlackReal K q
  let edgeSum : ℝ := ∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)
  let scale : ℝ := (Nat.factorial S.card : ℝ) * (slack / N ^ S.card)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := K)
  have hN_nonneg : 0 ≤ N := le_of_lt hN_pos
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale, slack, visibleNormalizerSlackReal, N]
    positivity
  have hSleq : S.card ≤ q := by
    have hSsub : S ⊆ coordinates q := by simpa using hSpow
    simpa [coordinates] using Finset.card_le_card hSsub
  have hmem : S.card ∈ Finset.Ico 2 (q + 1) := by
    simp [Finset.mem_Ico, hge, Nat.lt_succ_of_le hSleq]
  calc
    (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ((3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) *
        ((Nat.factorial S.card : ℝ) *
          (((Fintype.card K : ℝ) ^ q /
            (visibleNormalizerNNReal (G := K) (q := q) : ℝ)) /
            (Fintype.card K : ℝ) ^ S.card))) = edgeSum * scale := by
      simp [edgeSum, scale, slack, visibleNormalizerSlackReal, N, Finset.sum_mul,
        Mayer.card_pairClusterSupportEdges]
    _ ≤ partitionActivity S.card * scale := by
      exact mul_le_mul_of_nonneg_right (hpart S hSpow hS hge) hscale_nonneg
    _ ≤ (Nat.factorial S.card : ℝ) * partitionActivity S.card *
        (Cnorm / N ^ S.card) := by
      dsimp [scale, slack]
      have hden_nonneg : 0 ≤ N ^ S.card := pow_nonneg hN_nonneg _
      have hscale_le : slack / N ^ S.card ≤ Cnorm / N ^ S.card :=
        div_le_div_of_nonneg_right hslack hden_nonneg
      have hpa_nonneg : 0 ≤ partitionActivity S.card := hpart_nonneg S.card
      have hf_nonneg : 0 ≤ (Nat.factorial S.card : ℝ) := Nat.cast_nonneg _
      calc
        partitionActivity S.card * ((Nat.factorial S.card : ℝ) * (slack / N ^ S.card)) =
            (Nat.factorial S.card : ℝ) * partitionActivity S.card * (slack / N ^ S.card) := by
              ring
        _ ≤ (Nat.factorial S.card : ℝ) * partitionActivity S.card * (Cnorm / N ^ S.card) := by
          exact mul_le_mul_of_nonneg_left hscale_le (mul_nonneg hf_nonneg hpa_nonneg)
    _ ≤ localActivity S.card := hlocal S.card hmem

set_option maxHeartbeats 800000 in
/-- Centered-covering endpoint with scalar work split into normalizer slack,
support-partition edge summability, and the explicit ANOVA-centering factor. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity rawActivity localActivity : Nat → ℝ} {Cnorm Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hslack : visibleNormalizerSlackReal K q ≤ Cnorm)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hraw : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (Cnorm / (Fintype.card K : ℝ) ^ k) ≤ rawActivity k)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_factorialThreePowEdgeBudget_quadratic
    (K := K) (q := q) (rawActivity := rawActivity) (localActivity := localActivity)
    (Cconst := Cconst) hq hcovering ?_ hcenter hC hsmall hactivity
  exact rankCertifiedNormalizedUrsell_hscalar_of_partitionEdgeSummability
    (q := q) (K := K) (partitionActivity := partitionActivity)
    (localActivity := rawActivity) (Cnorm := Cnorm)
    hpart_nonneg hslack hpart hraw

set_option maxHeartbeats 800000 in
/-- Certified normalized-Ursell endpoint with scalar work split into normalizer
slack and support-partition edge summability. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cnorm Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hslack : visibleNormalizerSlackReal K q ≤ Cnorm)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (Cnorm / (Fintype.card K : ℝ) ^ k) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_factorialThreePowEdgeBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hselect ?_ hC hsmall hactivity
  exact rankCertifiedNormalizedUrsell_hscalar_of_partitionEdgeSummability
    (q := q) (K := K) (partitionActivity := partitionActivity)
    (localActivity := localActivity) (Cnorm := Cnorm)
    hpart_nonneg hslack hpart hlocal

set_option maxHeartbeats 800000 in
/-- Same endpoint as
`xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_partitionEdgeSummability_quadratic`,
but with the normalizer-slack premise stated directly as a falling-factorial
inequality. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_descFactorialSlack_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cnorm Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hnorm : ((Fintype.card K : ℝ) ^ (2 * q)) ≤
      Cnorm * (((Fintype.card K).descFactorial q *
        (Fintype.card K).descFactorial q : Nat) : ℝ))
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (Cnorm / (Fintype.card K : ℝ) ^ k) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_partitionEdgeSummability_quadratic
    (K := K) (q := q) (partitionActivity := partitionActivity)
    (localActivity := localActivity) (Cnorm := Cnorm) (Cconst := Cconst)
    hq hselect hpart_nonneg ?_ hpart hlocal hC hsmall hactivity
  exact visibleNormalizerSlackReal_le_of_pow_le_const_mul_descFactorial_sq
    (G := K) (q := q) hq hnorm

set_option maxHeartbeats 800000 in
/-- Centered-covering endpoint with the normalizer slack discharged by the
concrete small-query condition `q(q-1) ≤ |K|`.  The remaining analytic leaves
are support-partition/Penrose summability, the centering scalar bound, and the
usual local-activity tail bound. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_queryPairSlack_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity rawActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hraw : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (4 / (Fintype.card K : ℝ) ^ k) ≤ rawActivity k)
    (hcenter : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (S.powerset.card : ℝ) * rawActivity S.card ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  have hN : 0 < Fintype.card K := Fintype.card_pos (α := K)
  have hq : q ≤ Fintype.card K :=
    query_le_of_queryPair_le_card (Fintype.card K) q hN hquery
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_partitionEdgeSummability_quadratic
    (K := K) (q := q) (partitionActivity := partitionActivity)
    (rawActivity := rawActivity) (localActivity := localActivity)
    (Cnorm := 4) (Cconst := Cconst)
    hq hcovering hpart_nonneg ?_ hpart ?_ hcenter hC hsmall hactivity
  · exact visibleNormalizerSlackReal_le_four_of_queryPair_le_card K q hquery
  · simpa using hraw

set_option maxHeartbeats 800000 in
/-- Centered-covering endpoint with the ANOVA projection factor absorbed into
the scalar local-activity premise as `2^k`.  This is the clean theorem-facing
form of the current scalar branch: the remaining non-scalar inputs are the
centered covering contraction and support-partition/Penrose summability. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_queryPairSlack_partitionEdgeSummability_centeredActivity_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCenteredCoveringContraction (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (2 : ℝ) ^ k *
        ((Nat.factorial k : ℝ) * partitionActivity k *
          (4 / (Fintype.card K : ℝ) ^ k)) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_queryPairSlack_partitionEdgeSummability_quadratic
    (K := K) (q := q) (partitionActivity := partitionActivity)
    (rawActivity := fun k =>
      (Nat.factorial k : ℝ) * partitionActivity k *
        (4 / (Fintype.card K : ℝ) ^ k))
    (localActivity := localActivity) (Cconst := Cconst)
    hquery hcovering hpart_nonneg hpart ?_ ?_ hC hsmall hactivity
  · intro k hk
    exact le_rfl
  · intro S hSpow _hS hge
    have hSleq : S.card ≤ q := by
      have hSsub : S ⊆ coordinates q := by simpa using hSpow
      simpa [coordinates] using Finset.card_le_card hSsub
    have hmem : S.card ∈ Finset.Ico 2 (q + 1) := by
      simp [Finset.mem_Ico, hge, Nat.lt_succ_of_le hSleq]
    have hpowerset : (S.powerset.card : ℝ) = (2 : ℝ) ^ S.card := by
      exact_mod_cast (Finset.card_powerset S)
    simpa [hpowerset] using hlocal S.card hmem

set_option maxHeartbeats 800000 in
/-- Strongest current centered endpoint with the covering contraction split into
the base pair-support identity and the genuine higher-order Penrose/Ursell
identity. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_queryPairSlack_partitionEdgeSummability_centeredActivity_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hpair : ∀ S ∈ (coordinates q).powerset, S.card = 2 →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hlarge : ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (2 : ℝ) ^ k *
        ((Nat.factorial k : ℝ) * partitionActivity k *
          (4 / (Fintype.card K : ℝ) ^ k)) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_queryPairSlack_partitionEdgeSummability_centeredActivity_quadratic
    (K := K) (q := q) (partitionActivity := partitionActivity)
    (localActivity := localActivity) (Cconst := Cconst)
    hquery ?_ hpart_nonneg hpart hlocal hC hsmall hactivity
  exact rankCertifiedNormalizedUrsell_centeredCoveringContraction_of_pair_and_ge_three
    (q := q) (K := K) hpair hlarge

/-- Exact support-partition edge activity at a fixed support cardinality.  This
packages the `hpart` premise of the centered scalar endpoint into one finite
cardinality-indexed quantity; the remaining hard work is to prove this exact
quantity has the desired growth. -/
noncomputable def rankCertifiedSupportPartitionEdgeActivity (q k : Nat) : ℝ :=
  ∑ S ∈ (coordinates q).powersetCard k,
    ∑ i : Mayer.SupportPartitionClusters (q := q) S,
      (3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card)

/-- The exact support-partition edge activity is nonnegative. -/
theorem rankCertifiedSupportPartitionEdgeActivity_nonneg (q k : Nat) :
    0 ≤ rankCertifiedSupportPartitionEdgeActivity q k := by
  classical
  unfold rankCertifiedSupportPartitionEdgeActivity
  refine Finset.sum_nonneg ?_
  intro S _hS
  refine Finset.sum_nonneg ?_
  intro i _hi
  exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _

/-- Every fixed support contributes at most the exact support-partition edge
activity of its cardinality. -/
theorem rankCertifiedSupportPartitionEdgeActivity_bound
    {S : Finset (Fin q)} (hSpow : S ∈ (coordinates q).powerset) :
    (∑ i : Mayer.SupportPartitionClusters (q := q) S,
      (3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤
      rankCertifiedSupportPartitionEdgeActivity q S.card := by
  classical
  have hSsub : S ⊆ coordinates q := by
    simpa using hSpow
  have hmem : S ∈ (coordinates q).powersetCard S.card := by
    exact Finset.mem_powersetCard.mpr ⟨hSsub, rfl⟩
  unfold rankCertifiedSupportPartitionEdgeActivity
  calc
    (∑ i : Mayer.SupportPartitionClusters (q := q) S,
      (3 : ℝ) ^ (∑ B : i.1.parts,
        (Mayer.pairClusterSupportEdges (i.2 B)).card))
        = ∑ T ∈ ({S} : Finset (Finset (Fin q))),
            ∑ i : Mayer.SupportPartitionClusters (q := q) T,
              (3 : ℝ) ^ (∑ B : i.1.parts,
                (Mayer.pairClusterSupportEdges (i.2 B)).card) := by
          simp
    _ ≤ ∑ T ∈ (coordinates q).powersetCard S.card,
            ∑ i : Mayer.SupportPartitionClusters (q := q) T,
              (3 : ℝ) ^ (∑ B : i.1.parts,
                (Mayer.pairClusterSupportEdges (i.2 B)).card) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
          · intro T hT
            have hTS : T = S := by simpa using hT
            simpa [hTS] using hmem
          · intro T _hT _hTsingleton
            refine Finset.sum_nonneg ?_
            intro i _hi
            exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _

set_option maxHeartbeats 800000 in
/-- Strongest current centered endpoint with the support-partition summability
premise replaced by the exact cardinality-indexed edge activity. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_exactEdgeActivity_centeredActivity_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hpair : ∀ S ∈ (coordinates q).powerset, S.card = 2 →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hlarge : ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (2 : ℝ) ^ k *
        ((Nat.factorial k : ℝ) * rankCertifiedSupportPartitionEdgeActivity q k *
          (4 / (Fintype.card K : ℝ) ^ k)) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_queryPairSlack_partitionEdgeSummability_centeredActivity_quadratic
    (K := K) (q := q)
    (partitionActivity := rankCertifiedSupportPartitionEdgeActivity q)
    (localActivity := localActivity) (Cconst := Cconst)
    hquery hpair hlarge ?_ ?_ hlocal hC hsmall hactivity
  · exact rankCertifiedSupportPartitionEdgeActivity_nonneg q
  · intro S hSpow _hS _hge
    exact rankCertifiedSupportPartitionEdgeActivity_bound (q := q) hSpow

set_option maxHeartbeats 800000 in
/-- Strongest current centered endpoint with the scalar tail reduced to a pure
growth bound on the exact support-partition edge activity. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_exactEdgeActivity_growth_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hpair : ∀ S ∈ (coordinates q).powerset, S.card = 2 →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hlarge : ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
      RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S)
    (hC : 0 ≤ Cconst)
    (hedge : ∀ k ∈ Finset.Ico 2 (q + 1),
      (2 : ℝ) ^ k *
        ((Nat.factorial k : ℝ) * rankCertifiedSupportPartitionEdgeActivity q k * 4) ≤
          Cconst ^ k)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  let N : ℝ := Fintype.card K
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := K)
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_exactEdgeActivity_centeredActivity_quadratic
    (K := K) (q := q)
    (localActivity := fun k => (Cconst / (Fintype.card K : ℝ)) ^ k)
    (Cconst := Cconst)
    hquery hpair hlarge ?_ hC hsmall ?_
  · intro k hk
    have hden_nonneg : 0 ≤ N ^ k := pow_nonneg (le_of_lt hN_pos) _
    have hden_pos : 0 < N ^ k := pow_pos hN_pos _
    have hbase := hedge k hk
    dsimp [N] at hden_nonneg hden_pos
    calc
      (2 : ℝ) ^ k *
          ((Nat.factorial k : ℝ) * rankCertifiedSupportPartitionEdgeActivity q k *
            (4 / (Fintype.card K : ℝ) ^ k))
          = ((2 : ℝ) ^ k *
              ((Nat.factorial k : ℝ) * rankCertifiedSupportPartitionEdgeActivity q k * 4)) /
              (Fintype.card K : ℝ) ^ k := by
                field_simp [ne_of_gt hden_pos]
      _ ≤ Cconst ^ k / (Fintype.card K : ℝ) ^ k :=
            div_le_div_of_nonneg_right hbase hden_nonneg
      _ = (Cconst / (Fintype.card K : ℝ)) ^ k := by
            rw [div_pow]
  · intro k _hk
    exact le_rfl

/-- Named higher-support Penrose/Ursell obligation for the corrected centered
normalized-Ursell route. -/
def RankCertifiedNormalizedUrsellCenteredHigherSupportContractions
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K] : Prop :=
  ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
    RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction (q := q) K S

/-- Source-faithful higher-support ambient contraction for the corrected
centered normalized-Ursell route.  This is the genuine higher-order
Penrose/Ursell leaf after the canonical ambient selector has performed only
finite reindexing. -/
def RankCertifiedNormalizedUrsellCenteredCanonicalAmbientHigherContraction
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), Fintype (Mayer.SupportPartitionAmbientClusters (q := q) S)]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionAmbientClusters (q := q) S)] :
    Prop :=
  ∀ S ∈ (coordinates q).powerset, 3 ≤ S.card →
    (fun y => ∑ idx : Mayer.SupportPartitionAmbientClusters (q := q) S,
      Mayer.supportPartitionCanonicalAmbientFiberContribution (G := K) (q := q) S idx y) =
    fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
      anovaComponent S
        (rankCertifiedNormalizedUrsellSupportContribution (q := q) K S idx) y

/-- Named pure scalar growth obligation for the exact support-partition edge
activity. -/
def RankCertifiedSupportPartitionEdgeActivityGrowth (q : Nat) (Cconst : ℝ) : Prop :=
  ∀ k ∈ Finset.Ico 2 (q + 1),
    (2 : ℝ) ^ k *
      ((Nat.factorial k : ℝ) * rankCertifiedSupportPartitionEdgeActivity q k * 4) ≤
        Cconst ^ k

set_option maxHeartbeats 800000 in
/-- Current strongest theorem-facing XoP endpoint for the corrected centered
normalized-Ursell route, with all remaining work exposed as named obligations. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_named_obligations_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hpair : RankCertifiedNormalizedUrsellCenteredPairSupportContractions (q := q) K)
    (hlarge : RankCertifiedNormalizedUrsellCenteredHigherSupportContractions (q := q) K)
    (hC : 0 ≤ Cconst)
    (hedge : RankCertifiedSupportPartitionEdgeActivityGrowth q Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_exactEdgeActivity_growth_quadratic
    (K := K) (q := q) (Cconst := Cconst)
    hquery hpair hlarge hC hedge hsmall

set_option maxHeartbeats 800000 in
/-- Current strongest theorem-facing XoP endpoint with the base pair branch
lowered to the direct two-support ANOVA identity for `xopError`. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_anovaPair_named_obligations_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hpair : RankCertifiedNormalizedUrsellCenteredPairSupportAnovaIdentities (q := q) K)
    (hlarge : RankCertifiedNormalizedUrsellCenteredHigherSupportContractions (q := q) K)
    (hC : 0 ≤ Cconst)
    (hedge : RankCertifiedSupportPartitionEdgeActivityGrowth q Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_named_obligations_quadratic
    (K := K) (q := q) (Cconst := Cconst)
    hquery
    (rankCertifiedNormalizedUrsell_centeredPairSupportContractions_of_pairAnovaIdentities
      (q := q) (K := K) hpair)
    hlarge hC hedge hsmall

set_option maxHeartbeats 800000 in
/-- Certified normalized-Ursell endpoint with the normalizer slack discharged by
the concrete small-query condition `q(q-1) ≤ |K|`.  The remaining scalar leaves
are the genuine support-partition/Penrose summability estimate and the usual
local-activity tail bound. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_queryPairSlack_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hselect : RankCertifiedNormalizedUrsellCoveringFiberResummation (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (4 / (Fintype.card K : ℝ) ^ k) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  have hN : 0 < Fintype.card K := Fintype.card_pos (α := K)
  have hq : q ≤ Fintype.card K :=
    query_le_of_queryPair_le_card (Fintype.card K) q hN hquery
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_partitionEdgeSummability_quadratic
    (K := K) (q := q) (partitionActivity := partitionActivity)
    (localActivity := localActivity) (Cnorm := 4) (Cconst := Cconst)
    hq hselect hpart_nonneg ?_ hpart ?_ hC hsmall hactivity
  · exact visibleNormalizerSlackReal_le_four_of_queryPair_le_card K q hquery
  · simpa using hlocal

set_option maxHeartbeats 800000 in
/-- Source-faithful ambient-contraction version of the strongest current
rank-certified endpoint.  The direct support-cluster selector premise is
replaced by the canonical ambient contraction forced by covering families with
off-support vertices. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_canonicalAmbient_queryPairSlack_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hcontract : RankCertifiedNormalizedUrsellCanonicalAmbientContraction (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (4 / (Fintype.card K : ℝ) ^ k) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  have hN : 0 < Fintype.card K := Fintype.card_pos (α := K)
  have hq : q ≤ Fintype.card K :=
    query_le_of_queryPair_le_card (Fintype.card K) q hN hquery
  have hresum :
      Mayer.SupportPartitionWeightedResummationGeTwo (G := K) (q := q)
        (supportPartitionNormalizedUrsellWeight (q := q) K)
        (rankCertifiedSignedPairMayerBlockContribution (q := q) K) :=
    rankCertifiedNormalizedUrsell_weightedResummation_of_canonicalAmbientContraction
      (q := q) (K := K) hcontract
  refine xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hresum ?_ hC hsmall hactivity
  intro S hSpow hS hge
  have hindex :
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        rankCertifiedNormalizedUrsellIndexCardBudget (q := q) K S i) ≤
          localActivity S.card :=
    rankCertifiedNormalizedUrsell_sum_indexCardBudget_le_of_factorial_three_pow_edges
      (q := q) (K := K) (localActivity := localActivity) hq
      (rankCertifiedNormalizedUrsell_hscalar_of_partitionEdgeSummability
        (q := q) (K := K) (partitionActivity := partitionActivity)
        (localActivity := localActivity) (Cnorm := 4)
        hpart_nonneg
        (visibleNormalizerSlackReal_le_four_of_queryPair_le_card K q hquery)
        hpart
        (by simpa using hlocal)) S hSpow hS hge
  simpa [rankCertifiedNormalizedUrsellIndexCardBudget,
    rankCertifiedBlockChoiceAssignmentsCard, Finset.sum_const, nsmul_eq_mul,
    Finset.abs_prod, abs_mul, abs_div, div_eq_mul_inv, Finset.prod_const,
    Fintype.card_pi] using hindex

set_option maxHeartbeats 800000 in
/-- Covering-contraction version of the strongest current rank-certified
endpoint.  This exposes the exact remaining source-level Mayer/Ursell
cancellation leaf after canonical ambient finite reindexing has been removed. -/
theorem xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringContraction_queryPairSlack_partitionEdgeSummability_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {partitionActivity localActivity : Nat → ℝ} {Cconst : ℝ}
    (hquery : q * (q - 1) ≤ Fintype.card K)
    (hcovering : RankCertifiedNormalizedUrsellCoveringContraction (q := q) K)
    (hpart_nonneg : ∀ k, 0 ≤ partitionActivity k)
    (hpart : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        (3 : ℝ) ^ (∑ B : i.1.parts,
          (Mayer.pairClusterSupportEdges (i.2 B)).card)) ≤ partitionActivity S.card)
    (hlocal : ∀ k ∈ Finset.Ico 2 (q + 1),
      (Nat.factorial k : ℝ) * partitionActivity k *
        (4 / (Fintype.card K : ℝ) ^ k) ≤ localActivity k)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine
    xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_canonicalAmbient_queryPairSlack_partitionEdgeSummability_quadratic
      (K := K) (q := q) (partitionActivity := partitionActivity)
      (localActivity := localActivity) (Cconst := Cconst)
      hquery ?_ hpart_nonneg hpart hlocal hC hsmall hactivity
  exact rankCertifiedNormalizedUrsell_canonicalAmbientContraction_of_coveringContraction
    (q := q) (K := K) hcovering

/-- Concrete Ursell-weight version of the component-factorized resummation
endpoint.  The remaining `hresum` now has the standard partition-lattice
coefficient `(-1)^(m-1)(m-1)!` fixed in the statement. -/
theorem xop_advantageOn_injective_of_componentFactorized_ursellResummation_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset,
        anovaComponent S
          (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
      fun y => ∑ idx : Mayer.SupportPartitionClusters (q := q) S,
        Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
          (Mayer.supportPartitionUrsellWeight (q := q)) blockContribution S idx y)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
          (Mayer.supportPartitionUrsellWeight (q := q)) blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_componentFactorized_weightedResummation_globalSupportFullAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (Mayer.supportPartitionUrsellWeight (q := q)) blockContribution
    Term termFintype coeff atoms hq hresum heval hatoms hbudget hC hsmall hactivity

/-- Same as the previous theorem, but consuming the named
`SupportPartitionUrsellResummationGeTwo` obligation. -/
theorem xop_advantageOn_injective_of_ursellResummationGeTwo_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionUrsellResummationGeTwo (G := K) (q := q)
      blockContribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
          (Mayer.supportPartitionUrsellWeight (q := q)) blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  exact xop_advantageOn_injective_of_supportPartitionContribution_globalSupportFullAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
      (Mayer.supportPartitionUrsellWeight (q := q)) blockContribution)
    Term termFintype coeff atoms hq
    (Mayer.supportIndexedExpansionGeTwo_of_ursellResummationGeTwo
      (G := K) (q := q) blockContribution hresum)
    heval hatoms hbudget hC hsmall hactivity

/-- Same support-full-atomized endpoint, but with the resummation leaf reduced to
fiberwise covering sums over a selector into support-partition indices.

This is the current theorem-facing shape of the `hresum` branch: the finite
off-support cleanup and fiber reindexing are already proved in
`Mayer.supportPartitionUrsellResummationGeTwo_of_coveringFiber_resummation`;
the remaining premise is the genuine Ursell/Penrose identity on each selector
fiber. -/
theorem xop_advantageOn_injective_of_ursellCoveringFiberResummation_globalSupportFullAtomizedEval_cardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (select : (S : Finset (Fin q)) →
      S.Nonempty → 2 ≤ S.card → Finset (PairEdge (coordinates q)) →
        Mayer.SupportPartitionClusters (q := q) S)
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hfiber : ∀ S (_hSpow : S ∈ (coordinates q).powerset)
      (hS : S.Nonempty) (hge : 2 ≤ S.card),
      ∀ idx : Mayer.SupportPartitionClusters (q := q) S,
        (fun y => ∑ Γ ∈ (Finset.univ : Finset (PairEdge (coordinates q))).powerset.filter
            (fun Γ => S ⊆ edgeVertices Γ ∧ select S hS hge Γ = idx),
          anovaComponent S
            (componentFactorizedNormalizedPairFamilyTerm (G := K) Γ) y) =
        fun y =>
          Mayer.supportPartitionWeightedClusterProductContribution
            (G := K) (q := q) (Mayer.supportPartitionUrsellWeight (q := q))
            blockContribution S idx y)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionWeightedClusterProductContribution (G := K) (q := q)
          (Mayer.supportPartitionUrsellWeight (q := q)) blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ i : Mayer.SupportPartitionClusters (q := q) S,
        ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
          |coeff i t| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_globalSupportFullAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms hq ?_ heval hatoms
    hbudget hC hsmall hactivity
  exact Mayer.supportPartitionUrsellResummationGeTwo_of_coveringFiber_resummation
    (G := K) (q := q) blockContribution select hfiber

/-- Ursell-weighted endpoint from an unweighted global atomized evaluation.

If the block-product contribution has already been evaluated as a global
atomized hidden-fiber sum, the standard Ursell coefficient can be absorbed into
the scalar coefficients.  The numerical budget then pays the crude
`|(-1)^(m-1)(m-1)!| ≤ S.card!` factor supplied by `XoPMayer`. -/
theorem xop_advantageOn_injective_of_ursellResummationGeTwo_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionUrsellResummationGeTwo (G := K) (q := q)
      blockContribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            |coeff i t| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_globalSupportFullAtomizedEval_cardBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype
    (fun {S} i t => Mayer.supportPartitionUrsellWeight (q := q) S i * coeff i t)
    atoms hq hresum ?_ hatoms ?_ hC hsmall hactivity
  · intro S i y
    rw [Mayer.supportPartitionWeightedClusterProductContribution, heval]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    ring
  · intro S hSpow hS hge
    refine le_trans ?_ (hbudget S hSpow hS hge)
    let F : ℝ := Nat.factorial S.card
    let scale : ℝ := (Fintype.card K : ℝ) ^ (2 * q - S.card) /
      (Fintype.card K : ℝ) ^ q
    have hsum_le :
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            |Mayer.supportPartitionUrsellWeight (q := q) S i * coeff i t| *
              scale) ≤
        ∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            F * (|coeff i t| * scale) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      refine Finset.sum_le_sum ?_
      intro t _ht
      have hscale_nonneg : 0 ≤ scale := by
        dsimp [scale]
        positivity
      have hcoeff :
          |Mayer.supportPartitionUrsellWeight (q := q) S i * coeff i t| ≤
            F * |coeff i t| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by
            dsimp [F]
            exact Mayer.abs_supportPartitionUrsellWeight_le_factorial_card
              (q := q) S i)
          (abs_nonneg _)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
    refine le_trans hsum_le ?_
    simp [F, scale, Finset.mul_sum]

/-- Ursell endpoint from block-local atomized hidden-fiber evaluations.

This discharges the global `heval` premise of
`xop_advantageOn_injective_of_ursellResummationGeTwo_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic`
by expanding the support-partition product and assembling block-local hidden
fibers into one global hidden fiber. -/
theorem xop_advantageOn_injective_of_ursellResummationGeTwo_blockLocalAtomizedEval_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (BlockTerm : {S : Finset (Fin q)} → PairCluster S → Type*)
    [blockTermFintype : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      Fintype (BlockTerm C)]
    (blockCoeff : ∀ {S : Finset (Fin q)} (C : PairCluster S), BlockTerm C → ℝ)
    (blockAtoms : ∀ {S : Finset (Fin q)} (C : PairCluster S),
      BlockTerm C → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionUrsellResummationGeTwo (G := K) (q := q)
      blockContribution)
    (hblockEval : ∀ {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → K),
      blockContribution S C y =
        ∑ tB : BlockTerm C,
          blockCoeff C tB *
            (Fintype.card {aS : S → K //
              AtomFamilyHoldsOn (q := q) y (blockAtoms C tB) aS} : ℝ))
    (hblockAtoms : ∀ {S : Finset (Fin q)} (C : PairCluster S) (t : BlockTerm C),
      blockAtoms C t = pairFamilyFullAtoms (Mayer.pairClusterSupportEdges C))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ ((B : i.1.parts) → BlockTerm (i.2 B))
              (by infer_instance)),
            |((∏ B : i.1.parts, blockCoeff (i.2 B) (t B)) /
                (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  let Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type _ :=
    fun _S i => (B : i.1.parts) → BlockTerm (i.2 B)
  let termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i) := by
    intro S i
    dsimp [Term]
    infer_instance
  let coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ :=
    fun {S} i t =>
      (∏ B : i.1.parts, blockCoeff (i.2 B) (t B)) /
        (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ)
  let atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S) :=
    fun {_S} i t =>
      supportPartitionAtomFamily i.1
        (fun B : i.1.parts => blockAtoms (i.2 B) (t B))
  have heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ) := by
    intro S i y
    exact supportPartitionClusterProductContribution_eq_sum_pi_blockLocalAtomized
      (q := q) (K := K) blockContribution BlockTerm blockCoeff blockAtoms hblockEval i y
  have hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))) := by
    intro S i t
    dsimp [atoms]
    congr
    funext B
    exact hblockAtoms (i.2 B) (t B)
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms hq hresum heval hatoms
    hbudget hC hsmall hactivity

/-- Candidate concrete block contribution for the current full-atomization
route: a connected pair cluster contributes its support-local full
hidden/shifted atom fiber count. -/
def supportFullAtomizedBlockContribution
    [AddGroup G] [Fintype G] [DecidableEq G] :
    PairClusterContribution (G := G) (q := q) :=
  fun _S C y =>
    (Fintype.card {aS : _ → G //
      AtomFamilyHoldsOn (q := q) y
        (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges C)) aS} : ℝ)

theorem supportFullAtomizedBlockContribution_blockLocalEval
    [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset (Fin q)} (C : PairCluster S) (y : Fin q → G) :
    supportFullAtomizedBlockContribution (G := G) (q := q) S C y =
      ∑ _t : Unit,
        (1 : ℝ) *
          (Fintype.card {aS : S → G //
            AtomFamilyHoldsOn (q := q) y
              (pairFamilyFullAtoms (Mayer.pairClusterSupportEdges C)) aS} : ℝ) := by
  simp [supportFullAtomizedBlockContribution]

/-- Fully concrete full-atomized block-contribution endpoint.  The remaining
mathematical leaves are now the Ursell resummation for
`supportFullAtomizedBlockContribution` and the displayed factorial-paid scalar
budget. -/
theorem xop_advantageOn_injective_of_ursellResummationGeTwo_supportFullAtomizedBlockContribution_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionUrsellResummationGeTwo (G := K) (q := q)
      (supportFullAtomizedBlockContribution (G := K) (q := q)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
        (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ _t ∈ (@Finset.univ ((B : i.1.parts) → Unit) (by infer_instance)),
            |((∏ _B : i.1.parts, (1 : ℝ)) /
                (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ))| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_blockLocalAtomizedEval_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (supportFullAtomizedBlockContribution (G := K) (q := q))
    (fun {_S} _C => Unit)
    (fun {_S} _C _t => (1 : ℝ))
    (fun {_S} C _t => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges C))
    hq hresum ?_ ?_ hbudget hC hsmall hactivity
  · intro S C y
    exact supportFullAtomizedBlockContribution_blockLocalEval (G := K) (q := q) C y
  · intro S C t
    rfl

/-- Same concrete full-atomized endpoint with the `Unit` block-term sum
simplified to a cardinality factor for support-partition cluster indices. -/
theorem xop_advantageOn_injective_of_ursellResummationGeTwo_supportFullAtomizedBlockContribution_indexCardBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (hq : q ≤ Fintype.card K)
    (hresum : Mayer.SupportPartitionUrsellResummationGeTwo (G := K) (q := q)
      (supportFullAtomizedBlockContribution (G := K) (q := q)))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        ((Fintype.card (Mayer.SupportPartitionClusters (q := q) S) : ℝ) *
          (|1 / (Fintype.card ({j : Fin q // j ∉ S} → K) : ℝ)| *
            ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
              (Fintype.card K : ℝ) ^ q))) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_supportFullAtomizedBlockContribution_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    hq hresum ?_ hC hsmall hactivity
  intro S hSpow hS hge
  simpa [Finset.sum_const, nsmul_eq_mul, Finset.prod_const] using
    hbudget S hSpow hS hge

/-- Fully composed current endpoint: existential fiber-selector resummation plus
unweighted global support-full-atomized evaluation plus factorial scalar budget.

This is the narrowest theorem-facing form currently available in the main DAG.
It reduces the security proof to three concrete mathematical leaves: construct
the selector and prove its Ursell fiber identity, prove the unweighted global
atomized evaluation, and prove the factorial-paid scalar activity bound. -/
theorem xop_advantageOn_injective_of_existsUrsellCoveringFiber_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.SupportPartitionClusters (q := q) S)]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hselect : Mayer.SupportPartitionUrsellCoveringFiberResummationGeTwo
      (G := K) (q := q) blockContribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            |coeff i t| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms hq ?_ heval hatoms
    hbudget hC hsmall hactivity
  exact Mayer.supportPartitionUrsellResummationGeTwo_of_exists_coveringFiber_resummation
    (G := K) (q := q) blockContribution hselect

/-- Ambient-selector version of the current composed endpoint.  The resummation
leaf is supplied by source-faithful ambient fibers plus an explicit
ambient-to-Ursell contraction. -/
theorem xop_advantageOn_injective_of_ambientFiberContraction_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (ambientContribution : SupportIndexedContribution (G := K) (q := q)
      (Mayer.SupportPartitionAmbientClusters (q := q)))
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hfiber : Mayer.SupportPartitionAmbientFiberResummationGeTwo
      (G := K) (q := q) ambientContribution)
    (hcontract : Mayer.SupportPartitionAmbientToUrsellContractionGeTwo
      (G := K) (q := q) ambientContribution blockContribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            |coeff i t| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ursellResummationGeTwo_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms hq ?_ heval hatoms
    hbudget hC hsmall hactivity
  exact Mayer.supportPartitionUrsellResummationGeTwo_of_ambientFiber_contraction
    (G := K) (q := q) ambientContribution blockContribution hfiber hcontract

/-- Canonical ambient-fiber version of the composed endpoint.  The
source-faithful covering selector and its fiber resummation are now fixed by
`XoPMayer`; the only remaining resummation premise is the genuine
ambient-to-Ursell contraction. -/
theorem xop_advantageOn_injective_of_canonicalAmbientContraction_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hcontract : Mayer.SupportPartitionCanonicalAmbientToUrsellContractionGeTwo
      (G := K) (q := q) blockContribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            |coeff i t| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_ambientFiberContraction_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    (Mayer.supportPartitionCanonicalAmbientFiberContribution (G := K) (q := q))
    blockContribution Term termFintype coeff atoms hq ?_ hcontract heval hatoms
    hbudget hC hsmall hactivity
  exact Mayer.supportPartitionCanonicalAmbientFiberResummationGeTwo (G := K) (q := q)

/-- Covering-to-Ursell version of the composed endpoint.  The source-faithful
ambient selector and finite fiber reindexing are fully discharged in
`XoPMayer`; the resummation premise is now exactly the remaining
covering-family Ursell cancellation identity. -/
theorem xop_advantageOn_injective_of_coveringUrsell_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    {localActivity : Nat → ℝ} {Cconst : ℝ}
    (blockContribution : PairClusterContribution (G := K) (q := q))
    (Term : (S : Finset (Fin q)) → Mayer.SupportPartitionClusters (q := q) S → Type*)
    (termFintype : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S),
      Fintype (Term S i))
    (coeff : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → ℝ)
    (atoms : ∀ {S : Finset (Fin q)} (i : Mayer.SupportPartitionClusters (q := q) S),
      Term S i → Finset (Atom S))
    (hq : q ≤ Fintype.card K)
    (hcovering : Mayer.SupportPartitionCoveringUrsellContractionGeTwo
      (G := K) (q := q) blockContribution)
    (heval : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (y : Fin q → K),
      Mayer.supportPartitionClusterProductContribution (G := K) (q := q)
          blockContribution S i y =
        ∑ t : Term S i,
          coeff i t *
            (Fintype.card {a : Fin q → K //
              AtomFamilyHolds y a (atoms i t)} : ℝ))
    (hatoms : ∀ S (i : Mayer.SupportPartitionClusters (q := q) S) (t : Term S i),
      atoms i t =
        supportPartitionAtomFamily i.1
          (fun B : i.1.parts => pairFamilyFullAtoms (Mayer.pairClusterSupportEdges (i.2 B))))
    (hbudget : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (Nat.factorial S.card : ℝ) *
        (∑ i : Mayer.SupportPartitionClusters (q := q) S,
          ∑ t ∈ (@Finset.univ (Term S i) (termFintype S i)),
            |coeff i t| *
              ((Fintype.card K : ℝ) ^ (2 * q - S.card) /
                (Fintype.card K : ℝ) ^ q)) ≤ localActivity S.card)
    (hC : 0 ≤ Cconst)
    (hsmall : (q : ℝ) * (Cconst / (Fintype.card K : ℝ)) ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1),
      localActivity k ≤ (Cconst / (Fintype.card K : ℝ)) ^ k) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤
        Real.toNNReal (2 * Cconst ^ 2 * (q : ℝ) ^ 2 / (Fintype.card K : ℝ) ^ 2) := by
  refine xop_advantageOn_injective_of_canonicalAmbientContraction_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic
    (K := K) (q := q) (localActivity := localActivity) (Cconst := Cconst)
    blockContribution Term termFintype coeff atoms hq ?_ heval hatoms
    hbudget hC hsmall hactivity
  exact Mayer.supportPartitionCanonicalAmbientToUrsellContractionGeTwo_of_coveringUrsell
    (G := K) (q := q) blockContribution hcovering

/-- Probability-form codimension bound for connected nonempty pair-edge
families after full hidden/shifted atomization. -/
theorem pairFamilyFullAtoms_density_le_inv_pow_edgeVertices_of_connected_nonempty
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)} {r : Fin q}
    (hr : r ∈ edgeVertices Γ) (hconn : PairConnected Γ) (hΓ : Γ.Nonempty) :
    ((Fintype.card { ay : (Fin q → K) × (Fin q → K) //
        AtomFamilyHolds ay.2 ay.1 (pairFamilyFullAtoms Γ) } : NNReal) /
      (Fintype.card ((Fin q → K) × (Fin q → K)) : NNReal)) ≤
      1 / (Fintype.card K : NNReal) ^ (edgeVertices Γ).card := by
  have hroot : r ∈ atomVertices (pairFamilyFullAtoms Γ) := by
    simpa using hr
  have hreach : ∀ i ∈ atomVertices (pairFamilyFullAtoms Γ),
      Relation.ReflTransGen (atomLinked (pairFamilyFullAtoms Γ)) r i := by
    intro i hi
    have hi_edge : i ∈ edgeVertices Γ := by
      simpa using hi
    exact reachable_edgeLinked_to_atomLinked_pairFamilyFullAtoms (q := q) (hconn r hr i hi_edge)
  have hvis := hasVisibleObstruction_pairFamilyFullAtoms_of_nonempty (q := q) (K := K) hΓ
  have hbound :=
    atomFamily_joint_card_density_le_inv_pow_card_of_root_reaches_and_visibleObstruction
      (q := q) (K := K) (pairFamilyFullAtoms Γ) hroot hreach hvis
  simpa using hbound

/-- Exact normalized joint density of the full atomization of a pair-edge
family. -/
def pairFamilyFullAtomsJointDensity (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (Γ : Finset (PairEdge S)) : NNReal :=
  (Fintype.card { ay : (Fin q → K) × (Fin q → K) //
      AtomFamilyHolds ay.2 ay.1 (pairFamilyFullAtoms Γ) } : NNReal) /
    (Fintype.card ((Fin q → K) × (Fin q → K)) : NNReal)

/-- The simple codimension charge assigned to a pair cluster after full
atomization. -/
def fullAtomizedPairClusterCharge (K : Type*) [Fintype K]
    (S : Finset (Fin q)) (_C : PairCluster S) : ℝ :=
  ((1 / (Fintype.card K : NNReal) ^ S.card : NNReal) : ℝ)

/-- The simple full-atomized codimension charge is nonnegative. -/
theorem fullAtomizedPairClusterCharge_nonneg [Fintype K]
    (S : Finset (Fin q)) (C : PairCluster S) :
    0 ≤ fullAtomizedPairClusterCharge (q := q) K S C := by
  unfold fullAtomizedPairClusterCharge
  positivity

/-- Cluster contributions are charged by the exact full-atomized joint density.
The next theorem reduces this exact density charge to the simple
`|K|^{-|S|}` codimension charge. -/
def PairClusterFullAtomizedDensityChargeBound (K : Type*) [Field K] [Fintype K]
    [DecidableEq K]
    (contribution : PairClusterContribution (G := K) (q := q)) : Prop :=
  ∀ S (C : PairCluster S),
    visibleL1 (contribution S C) ≤ (pairFamilyFullAtomsJointDensity (q := q) K C.edges : ℝ)

/-- Density-definition wrapper around the connected full-atomization codimension
bound. -/
theorem pairFamilyFullAtomsJointDensity_le_inv_pow_edgeVertices_of_connected_nonempty
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} {Γ : Finset (PairEdge S)} {r : Fin q}
    (hr : r ∈ edgeVertices Γ) (hconn : PairConnected Γ) (hΓ : Γ.Nonempty) :
    pairFamilyFullAtomsJointDensity (q := q) K Γ ≤
      1 / (Fintype.card K : NNReal) ^ (edgeVertices Γ).card := by
  exact pairFamilyFullAtoms_density_le_inv_pow_edgeVertices_of_connected_nonempty
    (q := q) (K := K) hr hconn hΓ

/-- Every pair cluster's exact full-atomized density is bounded by the simple
charge `|K|^{-|S|}`. -/
theorem pairFamilyFullAtomsJointDensity_le_inv_pow_pairCluster
    [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (Fin q)} (C : PairCluster S) :
    pairFamilyFullAtomsJointDensity (q := q) K C.edges ≤
      1 / (Fintype.card K : NNReal) ^ S.card := by
  by_cases hS : S.Nonempty
  · rcases hS with ⟨r, hrS⟩
    have hrEdge : r ∈ edgeVertices C.edges := by
      rw [C.support_eq]
      exact hrS
    have hΓ : C.edges.Nonempty := pairCluster_edges_nonempty_of_support_nonempty C ⟨r, hrS⟩
    have hbound :=
      pairFamilyFullAtomsJointDensity_le_inv_pow_edgeVertices_of_connected_nonempty
        (q := q) (K := K) (S := coordinates q) (Γ := C.edges) hrEdge C.connected hΓ
    rwa [C.support_eq] at hbound
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hbound := atomFamily_joint_card_density_le_inv_pow_of_jointRank_ge
      (q := q) (K := K) (A := pairFamilyFullAtoms C.edges) (v := 0) (Nat.zero_le _)
    change pairFamilyFullAtomsJointDensity (q := q) K C.edges ≤
      1 / (Fintype.card K : NNReal) ^ 0 at hbound
    simpa [hzero] using hbound

/-- Exact full-atomized density charges imply the simple per-cluster
codimension charge interface consumed by `XoPMayer.lean`. -/
theorem pairClusterChargeBound_of_fullAtomizedDensityChargeBound
    [Field K] [Fintype K] [DecidableEq K]
    {contribution : PairClusterContribution (G := K) (q := q)}
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution) :
    Mayer.PairClusterChargeBound (G := K) (q := q) contribution
      (fullAtomizedPairClusterCharge (q := q) K) := by
  intro S C
  exact le_trans (hcharge S C) (by
    have hnn := pairFamilyFullAtomsJointDensity_le_inv_pow_pairCluster (q := q) (K := K) C
    change ((pairFamilyFullAtomsJointDensity (q := q) K C.edges : NNReal) : ℝ) ≤
      ((1 / (Fintype.card K : NNReal) ^ S.card : NNReal) : ℝ)
    exact_mod_cast hnn)

/-- End-to-end full-atomized charge endpoint: once the Penrose layer supplies a
pair-cluster expansion, exact full-atomized density domination, and summability
of the simple codimension charges, the concrete injective-input XoP advantage
bound follows. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hsum : (∑ S ∈ (coordinates q).powerset,
      ∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_pairClusterExpansion_charge (G := K) (q := q) ε
    hexp (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    hsum

/-- Full-atomized density endpoint with the summability hypothesis expressed
by support-size layers. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_layers
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlayers : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      Mayer.PairClusterChargeLayer (q := q) (fullAtomizedPairClusterCharge (q := q) K) k) ≤
        (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_charge_layers
    (G := K) (q := q) ε hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    hlayers

/-- Full-atomized density endpoint with an explicit Penrose tree-charge
summability handoff. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T)
    (hsum : (∑ S ∈ (coordinates q).powerset, ∑ T : Mayer.PairTree S, treeCharge S T) ≤
      (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge
    (G := K) (q := q) ε hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    htree hsum

/-- Full-atomized density endpoint with tree charges only over nonempty
supports and an explicit empty-component-zero premise. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_nonempty
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (hempty : visibleL1 (anovaComponent (∅ : Finset (Fin q)) (xopError (G := K) (q := q))) = 0)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (htree : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      ∑ T : Mayer.PairTree S, treeCharge S T) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty
    (G := K) (q := q) ε hempty hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    htree hsum

/-- Domain-sized full-atomized density endpoint over nonempty tree supports.
This discharges the empty ANOVA component through the normalized-counting
identity before entering the Penrose/rank handoff. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_nonempty_of_domain
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (htree : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      ∑ T : Mayer.PairTree S, treeCharge S T) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_of_domain
    (G := K) (q := q) ε hq hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    htree hsum

/-- Full-atomized density endpoint with Penrose tree charges summed by support
size. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_layers
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T)
    (hlayers : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      Mayer.PairTreeChargeLayer (q := q) treeCharge k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_layers
    (G := K) (q := q) ε hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    htree hlayers

/-- Full-atomized density endpoint with Penrose tree charges bounded by a
closed-form support-size activity. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_layerBound
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    {treeActivity : Nat → ℝ}
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T)
    (hlayer : ∀ k ∈ Finset.range ((coordinates q).card + 1),
      Mayer.PairTreeChargeLayer (q := q) treeCharge k ≤ treeActivity k)
    (hsum : (∑ k ∈ Finset.range ((coordinates q).card + 1), treeActivity k) ≤
      (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_layerBound
    (G := K) (q := q) ε hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    htree hlayer hsum

/-- Full-atomized density endpoint from a local Penrose tree support-size
activity and the corresponding binomial scalar sum. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_localActivity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K] (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    {localActivity : Nat → ℝ}
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (htree : ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T)
    (hlocal : ∀ S ∈ (coordinates q).powerset,
      (∑ T : Mayer.PairTree S, treeCharge S T) ≤ localActivity S.card)
    (hsum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      ((coordinates q).card.choose k : ℝ) * localActivity k) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_localActivity
    (G := K) (q := q) ε hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    htree hlocal hsum

/-- Tree-fiber domination implies the `htree` hypothesis required by the
Penrose tree-charge endpoint.  The selector is intentionally an input: the
Penrose stage may choose any spanning-tree selector, and the hard work is the
per-tree fiber estimate `hfiber`. -/
theorem fullAtomizedPairClusterCharge_htree_of_treeFiberBound [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (select : (S : Finset (Fin q)) → PairCluster S → Mayer.PairTree S)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ T : Mayer.PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => select S C = T),
        fullAtomizedPairClusterCharge (q := q) K S C) ≤ treeCharge S T) :
    ∀ S ∈ (coordinates q).powerset,
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T := by
  intro S hS
  classical
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (PairCluster S))) (g := select S)
    (f := fun C => fullAtomizedPairClusterCharge (q := q) K S C)]
  exact Finset.sum_le_sum (fun T _ => hfiber S hS T)

/-- Nonempty-support version of `fullAtomizedPairClusterCharge_htree_of_treeFiberBound`.
This is the tree-fiber bridge compatible with Mathlib's nonempty-tree
convention. -/
theorem fullAtomizedPairClusterCharge_htree_nonempty_of_treeFiberBound [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (select : (S : Finset (Fin q)) → S.Nonempty → PairCluster S → Mayer.PairTree S)
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : Mayer.PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => select S hS C = T),
        fullAtomizedPairClusterCharge (q := q) K S C) ≤ treeCharge S T) :
    ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T := by
  intro S hSpow hS
  classical
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (PairCluster S))) (g := select S hS)
    (f := fun C => fullAtomizedPairClusterCharge (q := q) K S C)]
  exact Finset.sum_le_sum (fun T _ => hfiber S hSpow hS T)

/-- Concrete nonempty tree-fiber bridge using the selected spanning tree from
each pair cluster.  This is the theorem-facing Penrose fiber interface: the
remaining hard estimate is now the per-selected-tree fiber bound `hfiber`. -/
theorem fullAtomizedPairClusterCharge_htree_nonempty_of_spanningTreeFiberBound [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {treeCharge : (S : Finset (Fin q)) → Mayer.PairTree S → ℝ}
    (hfiber : ∀ S ∈ (coordinates q).powerset, ∀ hS : S.Nonempty, ∀ T : Mayer.PairTree S,
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => Mayer.pairClusterSpanningTree C hS = T),
        fullAtomizedPairClusterCharge (q := q) K S C) ≤ treeCharge S T) :
    ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, treeCharge S T := by
  exact fullAtomizedPairClusterCharge_htree_nonempty_of_treeFiberBound
    (q := q) (K := K) (treeCharge := treeCharge)
    (select := fun S hS C => Mayer.pairClusterSpanningTree C hS)
    hfiber

/-- The exact charge of the cluster fiber whose selected spanning tree is `T`.
This is a theorem-facing object for the Penrose estimate: the hard bound is now
to control the sum of these selected-tree fibers by support size. -/
noncomputable def selectedSpanningTreeFiberCharge (K : Type*) [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (S : Finset (Fin q)) (T : Mayer.PairTree S) : ℝ :=
  if hS : S.Nonempty then
    ∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
        (fun C => Mayer.pairClusterSpanningTree C hS = T),
      fullAtomizedPairClusterCharge (q := q) K S C
  else 0

/-- The selected spanning-tree fiber charge is nonnegative. -/
theorem selectedSpanningTreeFiberCharge_nonneg [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (S : Finset (Fin q)) (T : Mayer.PairTree S) :
    0 ≤ selectedSpanningTreeFiberCharge (q := q) K S T := by
  classical
  unfold selectedSpanningTreeFiberCharge
  by_cases hS : S.Nonempty
  · simp [hS]
    exact Finset.sum_nonneg (fun C _ =>
      fullAtomizedPairClusterCharge_nonneg (q := q) (K := K) S C)
  · simp [hS]

/-- The total selected-tree fiber charge on a support is nonnegative. -/
theorem selectedSpanningTreeFiberCharge_sum_nonneg [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (S : Finset (Fin q)) :
    0 ≤ ∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T := by
  exact Finset.sum_nonneg (fun T _ =>
    selectedSpanningTreeFiberCharge_nonneg (q := q) (K := K) S T)

/-- Summing the exact selected spanning-tree fibers recovers the raw
full-atomized cluster charge.  This identity is diagnostic: without a genuine
Penrose/cumulant contribution replacing the raw positive charge, the tree
selector alone has not produced cancellation. -/
theorem selectedSpanningTreeFiberCharge_sum_eq_pairClusterCharge_sum [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) =
      ∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C := by
  classical
  simp [selectedSpanningTreeFiberCharge, hS]
  rw [Finset.sum_fiberwise]

/-- Total selected-tree fiber charge in cardinality form.  The explicit
`Fintype.card (PairCluster S)` factor is the formal obstruction to treating the
raw full-atomized selected fibers as the final Penrose bound. -/
theorem selectedSpanningTreeFiberCharge_sum_eq_pairCluster_card_mul [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {S : Finset (Fin q)} (hS : S.Nonempty) :
    (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) =
      (Fintype.card (PairCluster S) : ℝ) *
        (((1 / (Fintype.card K : NNReal) ^ S.card : NNReal) : ℝ)) := by
  rw [selectedSpanningTreeFiberCharge_sum_eq_pairClusterCharge_sum (q := q) (K := K) hS]
  simp [fullAtomizedPairClusterCharge, Finset.sum_const, nsmul_eq_mul]

/-- Diagnostic expansion of the exact selected-tree fiber charge.  This exposes
why the raw positive selected-fiber route is not itself a Penrose cancellation
proof: it still counts every cluster assigned to the tree. -/
theorem selectedSpanningTreeFiberCharge_eq_card_mul [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {S : Finset (Fin q)} (hS : S.Nonempty) (T : Mayer.PairTree S) :
    selectedSpanningTreeFiberCharge (q := q) K S T =
      (((Finset.univ : Finset (PairCluster S)).filter
          (fun C => Mayer.pairClusterSpanningTree C hS = T)).card : ℝ) *
        (((1 / (Fintype.card K : NNReal) ^ S.card : NNReal) : ℝ)) := by
  classical
  simp [selectedSpanningTreeFiberCharge, hS, fullAtomizedPairClusterCharge, Finset.sum_const,
    nsmul_eq_mul]

/-- The selected-tree fiber sum is bounded by its exact selected fiber charge. -/
theorem fullAtomizedPairClusterCharge_selectedSpanningTreeFiber_le
    [Fintype K] [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {S : Finset (Fin q)} (hS : S.Nonempty) (T : Mayer.PairTree S) :
    (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
        (fun C => Mayer.pairClusterSpanningTree C hS = T),
      fullAtomizedPairClusterCharge (q := q) K S C) ≤
        selectedSpanningTreeFiberCharge (q := q) K S T := by
  simp [selectedSpanningTreeFiberCharge, hS]

/-- The exact selected-tree fiber charge supplies the `htree` hypothesis over
nonempty supports. -/
theorem fullAtomizedPairClusterCharge_htree_nonempty_selectedSpanningTreeFiberCharge
    [Fintype K] [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)] :
    ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ C : PairCluster S, fullAtomizedPairClusterCharge (q := q) K S C) ≤
        ∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T := by
  exact fullAtomizedPairClusterCharge_htree_nonempty_of_spanningTreeFiberBound
    (q := q) (K := K) (treeCharge := selectedSpanningTreeFiberCharge (q := q) K)
    (fun S _hSpow hS T =>
      fullAtomizedPairClusterCharge_selectedSpanningTreeFiber_le
        (q := q) (K := K) hS T)

/-- Supports of size zero or one have no pair clusters, so their selected-tree
fiber charge is zero. -/
theorem selectedSpanningTreeFiberCharge_eq_zero_of_card_lt_two [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    {S : Finset (Fin q)} (hcard : S.card < 2) (T : Mayer.PairTree S) :
    selectedSpanningTreeFiberCharge (q := q) K S T = 0 := by
  classical
  by_cases hS : S.Nonempty
  · have hsum :
      (∑ C ∈ (Finset.univ : Finset (PairCluster S)).filter
          (fun C => Mayer.pairClusterSpanningTree C hS = T),
        fullAtomizedPairClusterCharge (q := q) K S C) = 0 := by
      exact Finset.sum_eq_zero (fun C _hC => by
        have htwo := Mayer.pairCluster_support_card_ge_two_of_nonempty C hS
        omega)
    simp [selectedSpanningTreeFiberCharge, hS, hsum]
  · simp [selectedSpanningTreeFiberCharge, hS]

/-- The remaining selected-tree Penrose local-activity obligation.  This is the
current hard leaf below the theorem path: prove that the exact selected-tree
fiber charge on every support of size at least two is controlled only by that
support size. -/
def SelectedSpanningTreeFiberLocalActivityBound (K : Type*) [Fintype K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (localActivity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
    (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) ≤
      localActivity S.card

/-- End-to-end rank endpoint using the exact selected spanning-tree fiber
charge and a remaining support-size local activity estimate. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_localActivity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) ≤
        localActivity S.card)
    (hsum : (∑ S ∈ (coordinates q).powerset.filter (fun S => S.Nonempty),
      localActivity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_of_domain
    (G := K) (q := q) ε hq hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    (fullAtomizedPairClusterCharge_htree_nonempty_selectedSpanningTreeFiberCharge
      (q := q) (K := K))
    hlocal hsum

/-- Selected spanning-tree fiber endpoint with the remaining summability already
reindexed by support cardinality. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_cardSum
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty →
      (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) ≤
        localActivity S.card)
    (hcardSum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      if k = 0 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k) ≤
        (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_cardSum_of_domain
    (G := K) (q := q) ε hq hexp
    (pairClusterChargeBound_of_fullAtomizedDensityChargeBound (q := q) (K := K) hcharge)
    (fullAtomizedPairClusterCharge_htree_nonempty_selectedSpanningTreeFiberCharge
      (q := q) (K := K))
    hlocal hcardSum

/-- Selected spanning-tree fiber endpoint where the local activity only needs
to be proved for supports of size at least two.  Size zero and one are
discharged from the pair-cluster support-cardinality lemma. -/
theorem xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_cardSum_ge_two
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlocal : ∀ S ∈ (coordinates q).powerset, S.Nonempty → 2 ≤ S.card →
      (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) ≤
        localActivity S.card)
    (hcardSum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      if k < 2 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k) ≤
        (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact
    xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_localActivity
      (K := K) (q := q) ε hq hexp hcharge
      (localActivity := fun k => if k < 2 then 0 else localActivity k)
      (fun S hSpow hS => by
        by_cases hlt : S.card < 2
        · have hzero :
            (∑ T : Mayer.PairTree S, selectedSpanningTreeFiberCharge (q := q) K S T) = 0 := by
              exact Finset.sum_eq_zero (fun T _ =>
                selectedSpanningTreeFiberCharge_eq_zero_of_card_lt_two (q := q) (K := K) hlt T)
          rw [hzero]
          simp [hlt]
        · have hge : 2 ≤ S.card := by omega
          simpa [hlt] using hlocal S hSpow hS hge)
      (by
        rwa [Mayer.nonemptySupportActivity_sum_by_card_ge_two (q := q) localActivity])

/-- Packaged endpoint from the named selected-tree local-activity obligation
and the cardinality-indexed scalar sum. -/
theorem xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {localActivity : Nat → ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlocal : SelectedSpanningTreeFiberLocalActivityBound (q := q) K localActivity)
    (hcardSum : (∑ k ∈ Finset.range ((coordinates q).card + 1),
      if k < 2 then 0 else ((coordinates q).card.choose k : ℝ) * localActivity k) ≤
        (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact
    xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_cardSum_ge_two
      (K := K) (q := q) ε hq hexp hcharge hlocal hcardSum

/-- Selected spanning-tree fiber endpoint with a scalar power activity bound.
This is the rank-path analogue of the pair-cluster Penrose scalar endpoint:
once the hard selected-fiber local activity is bounded by `a^k`, summability is
handled by the already-proved binomial tail estimate. -/
theorem xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity_pow_small
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlocal : SelectedSpanningTreeFiberLocalActivityBound (q := q) K localActivity)
    (ha : 0 ≤ a)
    (hsmall : ((coordinates q).card : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 ((coordinates q).card + 1), localActivity k ≤ a ^ k)
    (hε : 2 * ((((coordinates q).card : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity
    (K := K) (q := q) ε hq hexp hcharge hlocal
    (by
      rw [Mayer.sum_range_if_ge_two_eq_Ico]
      exact le_trans
        (Mayer.sum_Ico_choose_mul_le_of_activity_le ((coordinates q).card) hactivity)
        (le_trans
          (Mayer.sum_Ico_choose_mul_pow_le_two_mul_sq ((coordinates q).card) ha hsmall)
          hε))

/-- Query-count form of
`xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity_pow_small`. -/
theorem xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity_pow_small_q
    [Field K] [Fintype K] [DecidableEq K] [Nonempty K]
    [∀ S : Finset (Fin q), DecidableEq (Mayer.PairTree S)]
    (ε : NNReal)
    {contribution : PairClusterContribution (G := K) (q := q)}
    {localActivity : Nat → ℝ} {a : ℝ}
    (hq : q ≤ Fintype.card K)
    (hexp : PairClusterExpansion (G := K) (q := q) contribution)
    (hcharge : PairClusterFullAtomizedDensityChargeBound (q := q) K contribution)
    (hlocal : SelectedSpanningTreeFiberLocalActivityBound (q := q) K localActivity)
    (ha : 0 ≤ a)
    (hsmall : (q : ℝ) * a ≤ 1 / 2)
    (hactivity : ∀ k ∈ Finset.Ico 2 (q + 1), localActivity k ≤ a ^ k)
    (hε : 2 * (((q : ℝ) * a) ^ 2) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := K) (q := q)) (Model.xopIdealPDS (G := K) (q := q))
      (InjectiveInputs (X := K) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity_pow_small
    (K := K) (q := q) ε hq hexp hcharge hlocal ha
    (by simpa [coordinates] using hsmall)
    (by simpa [coordinates] using hactivity)
    (by simpa [coordinates] using hε)

/-- A pair-difference row is surjective as a linear form whenever the endpoints
are distinct. -/
theorem edgeDifferenceLinearForm_surjective [Field K] (e : (Fin q) × (Fin q))
    (hne : e.1 ≠ e.2) :
    Function.Surjective (edgeDifferenceLinearForm (q := q) K e) := by
  intro x
  classical
  refine ⟨fun i => if i = e.1 then x else 0, ?_⟩
  have hne' : e.2 ≠ e.1 := hne.symm
  simp [edgeDifferenceLinearForm, hne']

/-- The row family containing one atom. -/
def singleAtomRow {S : Finset (Fin q)} (A : Atom S) : PUnit → Atom S :=
  fun _ => A

/-- A single atom imposes one nontrivial hidden linear constraint. -/
theorem hiddenConstraintMap_singleAtom_surjective [Field K]
    {S : Finset (Fin q)} (A : Atom S) :
    Function.Surjective (hiddenConstraintMap (q := q) K (singleAtomRow A)) := by
  intro b
  have hne : A.edge.1.1 ≠ A.edge.1.2 := ne_of_lt A.edge.2.2.2
  rcases edgeDifferenceLinearForm_surjective (q := q) (K := K) A.edge.1 hne
      (b PUnit.unit) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  funext r
  cases r
  simpa [hiddenConstraintMap, singleAtomRow, atomLinearForm] using ha

/-- Base case for graph/rank lower bounds: one atom has hidden rank one. -/
theorem hiddenRank_singleAtom [Field K] {S : Finset (Fin q)} (A : Atom S) :
    hiddenRank (q := q) K (singleAtomRow A) = 1 := by
  unfold hiddenRank
  have hrange : (hiddenConstraintMap (q := q) K (singleAtomRow A)).range = ⊤ :=
    LinearMap.range_eq_top.mpr (hiddenConstraintMap_singleAtom_surjective (q := q) (K := K) A)
  rw [hrange]
  simp

@[simp]
theorem atomVertices_singleton {S : Finset (Fin q)} (A : Atom S) :
    atomVertices ({A} : Finset (Atom S)) = {A.edge.1.1, A.edge.1.2} := by
  simp [atomVertices]

theorem atomVertices_singleton_card {S : Finset (Fin q)} (A : Atom S) :
    (atomVertices ({A} : Finset (Atom S))).card = 2 := by
  have hne : A.edge.1.1 ≠ A.edge.1.2 := ne_of_lt A.edge.2.2.2
  simp [atomVertices_singleton, hne]

/-- Single-atom graph/rank lower bound in the intended `v - 1` form. -/
theorem hiddenRank_singleAtom_eq_atomVertices_card_sub_one [Field K]
    {S : Finset (Fin q)} (A : Atom S) :
    hiddenRank (q := q) K (singleAtomRow A) =
      (atomVertices ({A} : Finset (Atom S))).card - 1 := by
  rw [hiddenRank_singleAtom, atomVertices_singleton_card]

end Rank
end XoP
end Applications
end RandomSystems
