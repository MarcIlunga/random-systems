/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.Counting
import RandomSystems.DistSimp
import RandomSystems.StatDist

/-!
# Migrated SoP visible law

This module ports the fixed visible-output law from the old
`RandomSystems.Applications.SoP.Transcript` / `TV` layer to the `NextGen`
H-technique migration surface.

Source status:

* source theorem object: compatible hidden-state counts for a fixed visible
  output tuple;
* source theorem object: real and ideal visible-output masses;
* support lemma forced by formalization: expose those mass functions as
  `RandomSystems.Dist`s via the generic finite-mass adapter.

This file deliberately does not import the old `RandomSystems.Applications.SoP`
modules.  The next layer will connect these visible laws to concrete
`PFunPDE.transcriptLaw` instances.
-/

noncomputable section

open scoped BigOperators NNReal

namespace NextGen
namespace Migration
namespace HTechnique
namespace SoP

attribute [local instance] Classical.propDecidable

variable {G : Type*} {q : Nat}

/-- **Source theorem object.** A query-indexed tuple with no repeated entries. -/
def InjectiveTuple (a : Fin q → G) : Prop :=
  Function.Injective a

/-- **Source theorem object.** Number of injective tuples.  This is Mathlib's
falling factorial. -/
def injectiveTupleCount [Fintype G] : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter (fun a => InjectiveTuple a)).card

/-- **Source theorem bridge.** The injective tuple count is `(N)_q`. -/
@[simp]
theorem injectiveTupleCount_descFactorial [Fintype G] :
    injectiveTupleCount (G := G) (q := q) = (Fintype.card G).descFactorial q := by
  unfold injectiveTupleCount InjectiveTuple
  letI : Fintype { f : Fin q → G // Function.Injective f } :=
    Fintype.ofEquiv (Fin q ↪ G) (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G).symm
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G)]
  rw [Fintype.card_embedding_eq, Fintype.card_fin]

/-- **Source theorem object.** The subtype of injective hidden tuples. -/
def InjectiveTupleSubtype (G : Type*) (q : Nat) : Type _ :=
  { a : Fin q → G // InjectiveTuple a }

instance injectiveTupleSubtypeFintype [Fintype G] :
    Fintype (InjectiveTupleSubtype G q) :=
  Fintype.ofEquiv (Fin q ↪ G) (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G).symm

@[simp]
theorem injectiveTupleSubtype_card [Fintype G] :
    Fintype.card (InjectiveTupleSubtype G q) = @injectiveTupleCount G q _ := by
  letI : Fintype { f : Fin q → G // Function.Injective f } :=
    Fintype.ofEquiv (Fin q ↪ G) (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G).symm
  unfold InjectiveTupleSubtype injectiveTupleCount InjectiveTuple
  rw [← Fintype.card_subtype]
  rfl

/-- **Source theorem object.** Shift a hidden tuple by a visible output tuple. -/
def shifted [AddGroup G] (y a : Fin q → G) : Fin q → G :=
  fun i => a i + y i

/-- **Source theorem object.** A hidden tuple is compatible with visible outputs
when both the first permutation values and the shifted second permutation values
are injective. -/
def CompatibleHiddenState [AddGroup G] (y a : Fin q → G) : Prop :=
  Function.Injective a ∧ Function.Injective (shifted y a)

/-- **Source theorem object.** Visible-output/hidden-state compatible pairs. -/
def CompatiblePair (G : Type*) [AddGroup G] (q : Nat) : Type _ :=
  { p : (Fin q → G) × (Fin q → G) // CompatibleHiddenState p.1 p.2 }

/-- **Source theorem bridge.** Compatible `(y, a)` pairs are equivalent to pairs
of injective tuples `(a, b)`, where `b = a + y`. -/
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

/-- **Source theorem bridge.** Compatible pairs as a dependent sum over visible
outputs and compatible hidden states. -/
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

@[simp]
theorem compatiblePair_card [AddGroup G] [Fintype G] :
    Fintype.card (CompatiblePair G q) =
      @injectiveTupleCount G q _ * @injectiveTupleCount G q _ := by
  rw [Fintype.card_congr
    (compatiblePairEquivInjectiveProduct :
      CompatiblePair G q ≃ InjectiveTupleSubtype G q × InjectiveTupleSubtype G q)]
  simp [Fintype.card_prod]

local instance compatibleFiberFintype [AddGroup G] [Fintype G] (y : Fin q → G) :
    Fintype { a : Fin q → G // CompatibleHiddenState y a } :=
  Fintype.subtype
    ((Finset.univ : Finset (Fin q → G)).filter (fun a => CompatibleHiddenState y a))
    (by intro a; simp)

/-- **Source theorem object.** The number of compatible hidden tuples for a
fixed visible output tuple. -/
def compatibleCountNat [AddGroup G] [Fintype G] (y : Fin q → G) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter (fun a => CompatibleHiddenState y a)).card

@[simp]
theorem compatibleCountNat_eq_card_filter [AddGroup G] [Fintype G] (y : Fin q → G) :
    compatibleCountNat y =
      ((Finset.univ : Finset (Fin q → G)).filter
        (fun a => CompatibleHiddenState y a)).card := by
  rfl

/-- **Source theorem bridge; candidate for upstream.** For every visible output
tuple, there are at least `∏ k<q, (|G| - 2k)` compatible hidden tuples.  This is
the visible-law fiber-count lower bound used in the SoP H-technique ratio. -/
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

@[simp]
theorem compatibleFiber_card [AddGroup G] [Fintype G] (y : Fin q → G) :
    Fintype.card { a : Fin q → G // CompatibleHiddenState y a } =
      compatibleCountNat y := by
  unfold compatibleCountNat
  rw [← Fintype.card_subtype]

/-- **Source theorem bridge.** Summing compatible hidden-state counts over
visible tuples counts compatible pairs. -/
theorem sum_compatibleCountNat_eq_compatiblePair_card [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNat y) = Fintype.card (CompatiblePair G q) := by
  rw [Fintype.card_congr
    (compatiblePairEquivSigma :
      CompatiblePair G q ≃ Sigma (fun y : Fin q → G =>
        { a : Fin q → G // CompatibleHiddenState y a }))]
  rw [Fintype.card_sigma]
  simp [compatibleFiber_card]

/-- **Source theorem bridge.** The raw total compatible count is the square of
the injective-tuple count. -/
theorem sum_compatibleCountNat_eq_injectiveTupleCount_sq [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNat y) =
      @injectiveTupleCount G q _ * @injectiveTupleCount G q _ := by
  rw [sum_compatibleCountNat_eq_compatiblePair_card, compatiblePair_card]

/-- **Source theorem bridge.** The raw total compatible count is `(N)_q^2`. -/
theorem sum_compatibleCountNat_eq_descFactorial_sq [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNat y) =
      (Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q := by
  rw [sum_compatibleCountNat_eq_injectiveTupleCount_sq, injectiveTupleCount_descFactorial]

/-- **Source theorem object.** The compatible hidden-tuple count as an `NNReal`
mass numerator. -/
def compatibleCountNNReal [AddGroup G] [Fintype G] (y : Fin q → G) : NNReal :=
  (compatibleCountNat y : NNReal)

@[simp]
theorem compatibleCountNNReal_eq_coe_nat [AddGroup G] [Fintype G] (y : Fin q → G) :
    compatibleCountNNReal y = (compatibleCountNat y : NNReal) := by
  rfl

/-- **Source theorem bridge.** `NNReal` form of the total compatible count. -/
theorem sum_compatibleCountNNReal_eq_descFactorial_sq [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNNReal y) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        NNReal) := by
  change (∑ y : Fin q → G, (compatibleCountNat y : NNReal)) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        NNReal)
  rw [← Nat.cast_sum]
  rw [sum_compatibleCountNat_eq_descFactorial_sq]

/-- **Source theorem object.** Denominator for the real SoP visible-output law:
the number of pairs of injective hidden tuples, `(N)_q^2`. -/
def realVisibleDenominator [Fintype G] (q : Nat) : NNReal :=
  (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
    NNReal)

/-- **Source theorem object.** Exact real visible-output mass for a fixed tuple
`y`: `Z(y) / (N)_q^2`. -/
def realVisibleMass [AddGroup G] [Fintype G] (y : Fin q → G) : NNReal :=
  compatibleCountNNReal y / realVisibleDenominator (G := G) q

/-- **Source theorem object.** Exact ideal visible-output mass for a fixed tuple,
written as the uniform finite distribution. -/
def idealVisibleMass [Fintype G] [Nonempty G] (y : Fin q → G) : NNReal :=
  RandomSystems.Dist.uniform (Fin q → G) y

/-- **Source theorem object.** Real visible mass in closed numerator/denominator
form. -/
theorem realVisibleMass_eq [AddGroup G] [Fintype G] (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      compatibleCountNNReal y /
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) := by
  rfl

/-- **Source theorem object.** Ideal visible mass in closed form, `1 / N^q`. -/
theorem idealVisibleMass_eq [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleMass (G := G) (q := q) y =
      1 / ((Fintype.card G ^ q : Nat) : NNReal) := by
  simp [idealVisibleMass, RandomSystems.Dist.uniform_apply]

/-- **Source theorem object.** The expectation normalizer `E_I[Z] =
((N)_q)^2 / N^q`.  The `q <= N` assumption is kept at the use sites that need
nonzero denominators. -/
def expectationNormalizer [Fintype G] (q : Nat) : NNReal :=
  realVisibleDenominator (G := G) q / ((Fintype.card G ^ q : Nat) : NNReal)

/-- **Source theorem object.** Visible density ratio `Z(y) / E_I[Z]`. -/
def visibleDensityRatio [AddGroup G] [Fintype G] (y : Fin q → G) : NNReal :=
  compatibleCountNNReal y / expectationNormalizer (G := G) q

/-- **Source theorem bridge.** Visible density identity: real mass is density
ratio times ideal mass. -/
theorem realVisibleMass_eq_densityRatio_mul_ideal [AddGroup G] [Fintype G]
    [Nonempty G] (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      visibleDensityRatio (G := G) (q := q) y *
        idealVisibleMass (G := G) (q := q) y := by
  have hpow : (((Fintype.card G ^ q : Nat) : NNReal)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero q (Nat.ne_of_gt Fintype.card_pos))
  have hdesc_pos : 0 < (Fintype.card G).descFactorial q :=
    Nat.descFactorial_pos.mpr hq
  have hden : realVisibleDenominator (G := G) q ≠ 0 := by
    unfold realVisibleDenominator
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hdesc_pos) (Nat.ne_of_gt hdesc_pos))
  simp [realVisibleMass, realVisibleDenominator, visibleDensityRatio, expectationNormalizer,
    idealVisibleMass, RandomSystems.Dist.uniform_apply]
  rw [div_div_eq_mul_div]
  field_simp [hpow, hden]

/-- **Source theorem bridge.** Pointwise visible-law ratio bound for SoP:
under the paper's cubic query condition, every visible output has real mass at
least `(1 - q^3 / |G|^2)` times its ideal mass. -/
theorem realVisibleMass_lower_bound [AddGroup G] [Fintype G] [Nonempty G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) (y : Fin q → G) :
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        idealVisibleMass (G := G) (q := q) y ≤
      realVisibleMass (G := G) (q := q) y := by
  have h_pos : 0 < Fintype.card G := Fintype.card_pos
  calc
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        idealVisibleMass (G := G) (q := q) y
        = (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
            (1 / ((Fintype.card G : NNReal) ^ q)) := by
          rw [idealVisibleMass_eq]
          norm_num [Nat.cast_pow]
    _ ≤ ((((((Fintype.card G - q).factorial) ^ 2 *
            ∏ k ∈ Finset.range q, (Fintype.card G - 2 * k)) : Nat) : NNReal) /
          (((Fintype.card G).factorial : NNReal) ^ 2)) :=
          Counting.sop_ratio_counting_bound
            (size := Fintype.card G) (q := q) h_pos h_bound
    _ ≤ realVisibleMass (G := G) (q := q) y := by
          have hq_le : q ≤ Fintype.card G :=
            RandomSystems.CR18.Counting.q_le_of_cube_le_sq h_bound
          have h_count :
              ((∏ k ∈ Finset.range q, (Fintype.card G - 2 * k) : Nat) : NNReal) ≤
                compatibleCountNNReal (G := G) (q := q) y := by
            rw [compatibleCountNNReal_eq_coe_nat]
            exact_mod_cast compatibleCountNat_lower_bound (G := G) (q := q) y
          have hfact_nat :
              (Fintype.card G - q).factorial * (Fintype.card G).descFactorial q =
                (Fintype.card G).factorial :=
            Nat.factorial_mul_descFactorial hq_le
          have hfact :
              (((Fintype.card G - q).factorial : Nat) : NNReal) *
                  (((Fintype.card G).descFactorial q : Nat) : NNReal) =
                (((Fintype.card G).factorial : Nat) : NNReal) := by
            exact_mod_cast hfact_nat
          have hfac_ne : (((Fintype.card G - q).factorial : Nat) : NNReal) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero (Fintype.card G - q)
          have hdesc_pos : 0 < (Fintype.card G).descFactorial q :=
            Nat.descFactorial_pos.mpr hq_le
          have hdesc_ne : (((Fintype.card G).descFactorial q : Nat) : NNReal) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt hdesc_pos
          calc
            ((((((Fintype.card G - q).factorial) ^ 2 *
                    ∏ k ∈ Finset.range q, (Fintype.card G - 2 * k)) : Nat) : NNReal) /
                (((Fintype.card G).factorial : NNReal) ^ 2))
                = ((∏ k ∈ Finset.range q, (Fintype.card G - 2 * k) : Nat) : NNReal) /
                    ((((Fintype.card G).descFactorial q : Nat) : NNReal) ^ 2) := by
                  norm_num [Nat.cast_mul, Nat.cast_pow]
                  rw [← hfact]
                  field_simp [hfac_ne, hdesc_ne]
            _ ≤ compatibleCountNNReal (G := G) (q := q) y /
                ((((Fintype.card G).descFactorial q : Nat) : NNReal) ^ 2) := by
                  exact div_le_div_of_nonneg_right h_count (by positivity)
            _ = realVisibleMass (G := G) (q := q) y := by
                  rw [realVisibleMass_eq]
                  norm_num [Nat.cast_mul, pow_two]

/-- **Support lemma forced by formalization.** Real visible-output distribution
as a finite distribution. -/
abbrev realVisibleDist [AddGroup G] [Fintype G] :
    RandomSystems.Dist (Fin q → G) :=
  RandomSystems.Dist.ofFiniteMassFunction (realVisibleMass (G := G) (q := q))

/-- **Support lemma forced by formalization.** Ideal visible-output distribution
as a finite distribution. -/
abbrev idealVisibleDist [Fintype G] [Nonempty G] :
    RandomSystems.Dist (Fin q → G) :=
  RandomSystems.Dist.ofFiniteMassFunction (idealVisibleMass (G := G) (q := q))

@[simp]
theorem realVisibleDist_apply [AddGroup G] [Fintype G] (y : Fin q → G) :
    realVisibleDist (G := G) (q := q) y =
      realVisibleMass (G := G) (q := q) y := by
  simp [realVisibleDist]

@[simp]
theorem idealVisibleDist_apply [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleDist (G := G) (q := q) y =
      idealVisibleMass (G := G) (q := q) y := by
  simp [idealVisibleDist]

/-- **Support lemma forced by formalization.** The real visible law has total
mass one when `(N)_q` is nonzero, i.e. `q <= N`. -/
theorem realVisibleDist_weight [AddGroup G] [Fintype G] (hq : q ≤ Fintype.card G) :
    (realVisibleDist (G := G) (q := q)).weight = 1 := by
  have hdesc_pos : 0 < (Fintype.card G).descFactorial q :=
    Nat.descFactorial_pos.mpr hq
  have hden : realVisibleDenominator (G := G) q ≠ 0 := by
    unfold realVisibleDenominator
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hdesc_pos) (Nat.ne_of_gt hdesc_pos))
  calc
    (realVisibleDist (G := G) (q := q)).weight
        = ∑ y : Fin q → G, realVisibleMass (G := G) (q := q) y := by
            simp [realVisibleDist, RandomSystems.Dist.weight_ofFiniteMassFunction]
    _ = (∑ y : Fin q → G, compatibleCountNNReal (G := G) (q := q) y) /
          realVisibleDenominator (G := G) q := by
            simp [realVisibleMass, Finset.sum_div]
    _ = realVisibleDenominator (G := G) q / realVisibleDenominator (G := G) q := by
            rw [sum_compatibleCountNNReal_eq_descFactorial_sq]
            rfl
    _ = 1 := div_self hden

/-- **Support lemma forced by formalization.** The ideal visible law has total
mass one. -/
theorem idealVisibleDist_weight [Fintype G] [Nonempty G] :
    (idealVisibleDist (G := G) (q := q)).weight = 1 := by
  have hdist :
      idealVisibleDist (G := G) (q := q) =
        RandomSystems.Dist.uniform (Fin q → G) := by
    ext y
    simp [idealVisibleDist, idealVisibleMass]
  rw [hdist]
  simp only [dist_simp]

/-- **Support lemma forced by formalization.** The real and ideal visible laws
have equal total mass. -/
theorem realVisibleDist_weight_eq_ideal [AddGroup G] [Fintype G] [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight := by
  rw [realVisibleDist_weight (G := G) (q := q) hq, idealVisibleDist_weight]

/-- **Source theorem object.** Exact visible-output statistical distance for the
SoP fixed transcript law. -/
def visibleStatDist [AddGroup G] [Fintype G] [Nonempty G] : NNReal :=
  RandomSystems.statDist (realVisibleDist (G := G) (q := q))
    (idealVisibleDist (G := G) (q := q))

/-- **Source theorem object.** Expanded `statDist` formula for the exact visible
laws. -/
theorem visibleStatDist_eq_sum [AddGroup G] [Fintype G] [Nonempty G] :
    visibleStatDist (G := G) (q := q) =
      ∑ y : Fin q → G,
        (realVisibleMass (G := G) (q := q) y -
          idealVisibleMass (G := G) (q := q) y) := by
  simp [visibleStatDist, RandomSystems.statDist]

end SoP
end HTechnique
end Migration
end NextGen
