/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

/-!
# Compatible hidden-state counting

Dependency-light shared core for the SoP/XoP compatible hidden-state counts.
For a visible output tuple `y`, a hidden tuple `a` is compatible when both `a`
and `a + y` are injective.

This module owns the definitional layer and the counting facts that were
previously duplicated between `RandomSystems.Applications.XoPCombinatorics`
and the migrated H-technique SoP visible law
(`RandomSystems.HTechnique.SoP.VisibleLaw`).  Both of those modules now
alias this core; the anti-drift pins in
`RandomSystems.HTechnique.SoP.LegacyVisibleEquiv` certify that the
aliasing preserved the semantics.

It deliberately imports Mathlib only: no `Dist`, no PDS/PDE, no transcript or
application carriers.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace CompatibleCount

attribute [local instance] Classical.propDecidable

variable {G : Type*} {q : Nat}

/-- A query-indexed tuple with no repeated entries. -/
def InjectiveTuple (a : Fin q → G) : Prop :=
  Function.Injective a

/-- Number of injective hidden tuples.  This is Mathlib's falling factorial. -/
def injectiveTupleCount [Fintype G] : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter (fun a => InjectiveTuple a)).card

/--
The injective tuple count is `(N)_q`.  The proof is only the adapter shape:
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

/-- Hidden-state compatibility for one visible output tuple. -/
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

instance compatibleFiberFintype [AddGroup G] [Fintype G] (y : Fin q → G) :
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

/-- For every visible output tuple, there are at least `∏ k<q, (|G| - 2k)`
compatible hidden tuples.  This is the visible-law fiber-count lower bound used
in the SoP H-technique ratio. -/
theorem compatibleCountNat_lower_bound [AddGroup G] [Fintype G] (y : Fin q → G) :
    ∏ k ∈ Finset.range q, (Fintype.card G - 2 * k) ≤ compatibleCountNat y := by
  induction q with
  | zero =>
      change 1 ≤ compatibleCountNat y
      refine Finset.one_le_card.mpr ?_
      refine ⟨default, ?_⟩
      simp [CompatibleHiddenState]
      constructor <;> intro i <;> exact Fin.elim0 i
  | succ m ih =>
      let yInit : Fin m → G := fun i => y i.castSucc
      let yLast : G := y (Fin.last m)
      let compatibleInit : Finset (Fin m → G) :=
        Finset.univ.filter fun a => CompatibleHiddenState yInit a
      let prev : (Fin m → G) → Finset G := fun a => Finset.univ.image a
      let prevShift : (Fin m → G) → Finset G := fun a =>
        Finset.univ.image fun i => shifted yInit a i - yLast
      let allowed : (Fin m → G) → Finset G := fun a =>
        Finset.univ \ (prev a ∪ prevShift a)
      have ih' :
          ∏ k ∈ Finset.range m, (Fintype.card G - 2 * k) ≤ compatibleInit.card := by
        simpa [compatibleInit, compatibleCountNat] using ih yInit
      have h_allowed_card :
          ∀ a ∈ compatibleInit, Fintype.card G - 2 * m ≤ (allowed a).card := by
        intro a ha
        have ha' : CompatibleHiddenState yInit a := by
          simpa [compatibleInit] using ha
        rcases ha' with ⟨ha_inj, hshift_inj⟩
        have h_prev_card : (prev a).card = m := by
          simpa [prev] using
            (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin m)))
              (f := a) ha_inj)
        have h_prevShift_inj : Function.Injective (fun i : Fin m => shifted yInit a i - yLast) :=
          (sub_left_injective (b := yLast)).comp hshift_inj
        have h_prevShift_card : (prevShift a).card = m := by
          simpa [prevShift] using
            (Finset.card_image_of_injective
              (s := (Finset.univ : Finset (Fin m)))
              (f := fun i : Fin m => shifted yInit a i - yLast)
              h_prevShift_inj)
        have h_union_le : ((prev a) ∪ (prevShift a)).card ≤ 2 * m := by
          calc
            ((prev a) ∪ (prevShift a)).card ≤ (prev a).card + (prevShift a).card :=
              Finset.card_union_le _ _
            _ = m + m := by rw [h_prev_card, h_prevShift_card]
            _ = 2 * m := by ring
        have h_allowed_card_eq :
            (allowed a).card = Fintype.card G - ((prev a) ∪ (prevShift a)).card := by
          have hsubset : (prev a ∪ prevShift a) ⊆ (Finset.univ : Finset G) := by simp
          simpa [allowed] using Finset.card_sdiff_of_subset hsubset
        calc
          Fintype.card G - 2 * m ≤
              Fintype.card G - ((prev a) ∪ (prevShift a)).card :=
            Nat.sub_le_sub_left h_union_le (Fintype.card G)
          _ = (allowed a).card := h_allowed_card_eq.symm
      let extend : (Sigma fun _ : Fin m → G => G) → Fin (m + 1) → G := fun x =>
        Fin.snoc x.1 x.2
      have h_mapsTo :
          Set.MapsTo extend ↑(compatibleInit.sigma allowed)
            ↑((Finset.univ : Finset (Fin (m + 1) → G)).filter
              (fun a => CompatibleHiddenState y a)) := by
        intro x hx
        rcases x with ⟨a, aLast⟩
        have hx' : a ∈ compatibleInit ∧ aLast ∈ allowed a := by
          simpa [Finset.mem_sigma] using hx
        rcases hx' with ⟨ha, haLast⟩
        have ha' : CompatibleHiddenState yInit a := by
          simpa [compatibleInit] using ha
        rcases ha' with ⟨ha_inj, hshift_inj⟩
        have haLast_mem : aLast ∈ Finset.univ \ (prev a ∪ prevShift a) := by
          simpa [allowed] using haLast
        have haLast_not_union : aLast ∉ prev a ∪ prevShift a :=
          (Finset.mem_sdiff.mp haLast_mem).2
        have haLast_not_prev : aLast ∉ prev a := by
          intro hmem
          exact haLast_not_union (Finset.mem_union.mpr (Or.inl hmem))
        have haLast_not_prevShift : aLast ∉ prevShift a := by
          intro hmem
          exact haLast_not_union (Finset.mem_union.mpr (Or.inr hmem))
        have haLast_not_range : aLast ∉ Set.range a := by
          rintro ⟨i, rfl⟩
          exact haLast_not_prev (by simp [prev])
        have h_inj_snoc : Function.Injective (Fin.snoc a aLast) :=
          Fin.snoc_injective_of_injective ha_inj haLast_not_range
        have h_shift_not_range : aLast + yLast ∉ Set.range (shifted yInit a) := by
          rintro ⟨i, hi⟩
          apply haLast_not_prevShift
          refine Finset.mem_image.mpr ?_
          refine ⟨i, by simp, ?_⟩
          calc
            shifted yInit a i - yLast = (aLast + yLast) - yLast := by rw [← hi]
            _ = aLast := by simp
        have h_shift_eq :
            shifted y (Fin.snoc (α := fun _ => G) a aLast) =
              (Fin.snoc (α := fun _ => G) (shifted yInit a) (aLast + yLast) :
                Fin (m + 1) → G) := by
          funext i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simp [shifted, yInit]
          · simp [shifted, yLast]
        have h_shift_inj_snoc : Function.Injective (shifted y (Fin.snoc a aLast)) := by
          rw [h_shift_eq]
          exact Fin.snoc_injective_of_injective hshift_inj h_shift_not_range
        change extend ⟨a, aLast⟩ ∈
          ((Finset.univ : Finset (Fin (m + 1) → G)).filter
            (fun a => CompatibleHiddenState y a))
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h_inj_snoc, h_shift_inj_snoc⟩
      have h_injOn :
          Set.InjOn extend ↑(compatibleInit.sigma allowed) := by
        intro x hx z hz hxz
        rcases x with ⟨a, aLast⟩
        rcases z with ⟨b, bLast⟩
        dsimp [extend] at hxz
        rcases Fin.snoc_injective2 hxz with ⟨hab, hlast⟩
        subst hab
        subst hlast
        rfl
      have h_sigma_le :
          (compatibleInit.sigma allowed).card ≤ compatibleCountNat y := by
        have h :=
          Finset.card_le_card_of_injOn extend h_mapsTo h_injOn
        simpa [compatibleCountNat] using h
      have h_sigma_ge :
          compatibleInit.card * (Fintype.card G - 2 * m) ≤
            (compatibleInit.sigma allowed).card := by
        rw [Finset.card_sigma]
        calc
          compatibleInit.card * (Fintype.card G - 2 * m)
              = ∑ a ∈ compatibleInit, (Fintype.card G - 2 * m) := by simp
          _ ≤ ∑ a ∈ compatibleInit, (allowed a).card := by
              exact Finset.sum_le_sum (fun a ha => h_allowed_card a ha)
      calc
        ∏ k ∈ Finset.range (m + 1), (Fintype.card G - 2 * k)
            = (∏ k ∈ Finset.range m, (Fintype.card G - 2 * k)) *
                (Fintype.card G - 2 * m) := by
              simp [Finset.prod_range_succ]
        _ ≤ compatibleInit.card * (Fintype.card G - 2 * m) := by
              exact Nat.mul_le_mul_right _ ih'
        _ ≤ (compatibleInit.sigma allowed).card := h_sigma_ge
        _ ≤ compatibleCountNat y := h_sigma_le

end CompatibleCount
end RandomSystems
