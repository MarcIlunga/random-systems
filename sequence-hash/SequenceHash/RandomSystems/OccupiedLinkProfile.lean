import RandomSystems.CausalFiniteProduct
import RandomSystems.Counting
import SequenceHash.RandomSystems.OccupiedLink

/-!
# Causal occupied-link profiles

This module lifts the exact one-input common carrier to an arbitrary finite
family of construction inputs.  The full family is sampled first and an
arbitrary deterministic observation is applied afterwards.  Such an
observation includes every reveal order: construction-first, primitive-first,
and adaptive interleavings are all deterministic functions of the completed
profile once the external strategy is fixed.

The proof therefore has no chronological case list to maintain.  It builds the
product of the per-input common carriers, bounds the discarded product mass by
Weierstrass, and invokes data processing for the chosen observation.
-/

noncomputable section

open scoped BigOperators

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems

universe u v

/-! ## A finite product on the migrated real-mass carrier -/

/-- Independent product of a finite indexed family of finite distributions. -/
def finiteProduct {A : Type u} [Fintype A] {n : ℕ}
    (laws : Fin n → RandomSystems.Dist A) :
    RandomSystems.Dist (Fin n → A) :=
  RandomSystems.Dist.ofFiniteMassFunction fun values =>
    ∏ index, laws index (values index)

@[simp]
theorem finiteProduct_apply {A : Type u} [Fintype A] {n : ℕ}
    (laws : Fin n → RandomSystems.Dist A) (values : Fin n → A) :
    finiteProduct laws values = ∏ index, laws index (values index) := by
  simp [finiteProduct]

/-- The product weight factors into the product of component weights. -/
theorem finiteProduct_weight {A : Type u} [Fintype A] {n : ℕ}
    (laws : Fin n → RandomSystems.Dist A) :
    (finiteProduct laws).weight = ∏ index, (laws index).weight := by
  rw [finiteProduct, RandomSystems.Dist.weight_ofFiniteMassFunction]
  simp_rw [RandomSystems.Dist.weight_eq_sum]
  exact (Finset.prod_univ_sum _ fun index value => laws index value).symm

/-- Products of nonnegative laws are nonnegative. -/
theorem finiteProduct_nonNeg {A : Type u} [Fintype A] {n : ℕ}
    {laws : Fin n → RandomSystems.Dist A}
    (nonnegative : ∀ index, (laws index).NonNeg) :
    (finiteProduct laws).NonNeg := by
  intro values
  rw [finiteProduct_apply]
  exact Finset.prod_nonneg fun index _member =>
    nonnegative index (values index)

/-- Products of probability laws are probability laws. -/
theorem finiteProduct_isProbDist {A : Type u} [Fintype A] {n : ℕ}
    {laws : Fin n → RandomSystems.Dist A}
    (probability : ∀ index, (laws index).isProbDist) :
    (finiteProduct laws).isProbDist := by
  constructor
  · exact finiteProduct_nonNeg fun index => (probability index).nonNeg
  · rw [finiteProduct_weight]
    simp_rw [(probability _).weight_eq]
    simp

/-- Pointwise domination is preserved by finite independent products. -/
theorem finiteProduct_le {A : Type u} [Fintype A] {n : ℕ}
    {left right : Fin n → RandomSystems.Dist A}
    (leftNonnegative : ∀ index, (left index).NonNeg)
    (dominated : ∀ index value, left index value ≤ right index value)
    (values : Fin n → A) :
    finiteProduct left values ≤ finiteProduct right values := by
  rw [finiteProduct_apply, finiteProduct_apply]
  exact Finset.prod_le_prod
    (fun index _member => leftNonnegative index (values index))
    (fun index _member => dominated index (values index))

/-! ## Common-carrier product bound -/

/-- Any law dominated by both sides is a common carrier.  Their distance is
at most the first law's mass outside it. -/
theorem statDist_le_weight_sub_common {A : Type u} [Fintype A]
    {real ideal common : RandomSystems.Dist A}
    (common_le_real : ∀ value, common value ≤ real value)
    (common_le_ideal : ∀ value, common value ≤ ideal value) :
    statDist real ideal ≤ real.weight - common.weight := by
  rw [statDist_eq_sum_univ, RandomSystems.Dist.weight_eq_sum,
    RandomSystems.Dist.weight_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro value _member
  apply max_le
  · linarith [common_le_ideal value]
  · linarith [common_le_real value]

variable {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Real completed link profile for `n` activated construction inputs. -/
def occupiedLinkProfileReal {n : ℕ} (occupied : Fin n → Finset C)
    (stored : Fin n → C → C) : RandomSystems.Dist (Fin n → C × C) :=
  finiteProduct fun index =>
    occupiedLinkReal (occupied index) (stored index)

/-- Independent ideal completed link profile. -/
def occupiedLinkProfileIdeal {n : ℕ} :
    RandomSystems.Dist (Fin n → C × C) :=
  finiteProduct fun _index => occupiedLinkIdeal

/-- Product of the exact one-input common carriers. -/
def occupiedLinkProfileCommon {n : ℕ} (occupied : Fin n → Finset C)
    (stored : Fin n → C → C) : RandomSystems.Dist (Fin n → C × C) :=
  finiteProduct fun index =>
    occupiedLinkCommon (occupied index) (stored index)

theorem occupiedLinkProfileReal_isProbDist {n : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C) :
    (occupiedLinkProfileReal occupied stored).isProbDist := by
  exact finiteProduct_isProbDist fun index =>
    occupiedLinkReal_isProbDist (occupied index) (stored index)

theorem occupiedLinkProfileIdeal_isProbDist {n : ℕ} :
    (occupiedLinkProfileIdeal (C := C) (n := n)).isProbDist := by
  exact finiteProduct_isProbDist fun _index =>
    occupiedLinkIdeal_isProbDist

theorem occupiedLinkProfileCommon_nonNeg {n : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C) :
    (occupiedLinkProfileCommon occupied stored).NonNeg := by
  exact finiteProduct_nonNeg fun index =>
    occupiedLinkCommon_nonNeg (occupied index) (stored index)

theorem occupiedLinkProfileCommon_le_real {n : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C)
    (values : Fin n → C × C) :
    occupiedLinkProfileCommon occupied stored values ≤
      occupiedLinkProfileReal occupied stored values := by
  exact finiteProduct_le
    (fun index => occupiedLinkCommon_nonNeg
      (occupied index) (stored index))
    (fun index value => occupiedLinkCommon_le_real
      (occupied index) (stored index) value)
    values

theorem occupiedLinkProfileCommon_le_ideal {n : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C)
    (values : Fin n → C × C) :
    occupiedLinkProfileCommon occupied stored values ≤
      occupiedLinkProfileIdeal values := by
  exact finiteProduct_le
    (fun index => occupiedLinkCommon_nonNeg
      (occupied index) (stored index))
    (fun index value => occupiedLinkCommon_le_ideal
      (occupied index) (stored index) value)
    values

/-- The completed real and ideal profiles differ by at most the sum of their
exact per-input occupied-link charges. -/
theorem occupiedLinkProfile_statDist_le_sum {n : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C) :
    statDist (occupiedLinkProfileReal occupied stored)
        occupiedLinkProfileIdeal ≤
      ∑ index, statDist
        (occupiedLinkReal (occupied index) (stored index))
        occupiedLinkIdeal := by
  let distance : Fin n → ℝ := fun index =>
    statDist (occupiedLinkReal (occupied index) (stored index))
      occupiedLinkIdeal
  have distance_nonnegative : ∀ index, 0 ≤ distance index := fun index =>
    statDist_nonneg _ _
  have distance_le_one : ∀ index, distance index ≤ 1 := by
    intro index
    exact (statDist_le_weight
      (occupiedLinkReal_isProbDist
        (occupied index) (stored index)).nonNeg
      occupiedLinkIdeal_isProbDist.nonNeg).trans_eq
        (occupiedLinkReal_isProbDist
          (occupied index) (stored index)).weight_eq
  have productLower :=
    RandomSystems.CR18.Counting.one_sub_sum_le_prod_one_sub Finset.univ
      distance (fun index _ => distance_nonnegative index)
      (fun index _ => distance_le_one index)
  calc
    statDist (occupiedLinkProfileReal occupied stored)
          occupiedLinkProfileIdeal ≤
        (occupiedLinkProfileReal occupied stored).weight -
          (occupiedLinkProfileCommon occupied stored).weight :=
      statDist_le_weight_sub_common
        (occupiedLinkProfileCommon_le_real occupied stored)
        (occupiedLinkProfileCommon_le_ideal occupied stored)
    _ = 1 - ∏ index, (1 - distance index) := by
      rw [(occupiedLinkProfileReal_isProbDist occupied stored).weight_eq,
        occupiedLinkProfileCommon, finiteProduct_weight]
      simp_rw [occupiedLinkCommon_weight]
      simp only [distance]
    _ ≤ ∑ index, distance index := by
      linarith
    _ = ∑ index, statDist
          (occupiedLinkReal (occupied index) (stored index))
          occupiedLinkIdeal := rfl

/-- Closed exact-charge form of the product bound. -/
theorem occupiedLinkProfile_statDist_le_closed {n : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C) :
    statDist (occupiedLinkProfileReal occupied stored)
        occupiedLinkProfileIdeal ≤
      ∑ index,
        (occupied index).card * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
  refine (occupiedLinkProfile_statDist_le_sum occupied stored).trans_eq ?_
  apply Finset.sum_congr rfl
  intro index _member
  exact occupiedLink_statDist (occupied index) (stored index)

/-- Uniform `q`-row and `a`-input budget for the full causal profile. -/
theorem occupiedLinkProfile_statDist_le_budget {n q a : ℕ}
    (occupied : Fin n → Finset C) (stored : Fin n → C → C)
    (occupiedCard : ∀ index, (occupied index).card ≤ q)
    (inputCard : n ≤ a) :
    statDist (occupiedLinkProfileReal occupied stored)
        occupiedLinkProfileIdeal ≤
      (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  let charge : ℝ := ((Fintype.card C : ℝ) - 1) /
    (Fintype.card C : ℝ) ^ 2
  have charge_nonnegative : 0 ≤ charge := by
    have card_one : (1 : ℝ) ≤ Fintype.card C := by
      exact_mod_cast Fintype.card_pos (α := C)
    exact div_nonneg (sub_nonneg.mpr card_one) (sq_nonneg _)
  calc
    statDist (occupiedLinkProfileReal occupied stored)
          occupiedLinkProfileIdeal ≤
        ∑ index,
          (occupied index).card * ((Fintype.card C : ℝ) - 1) /
            (Fintype.card C : ℝ) ^ 2 :=
      occupiedLinkProfile_statDist_le_closed occupied stored
    _ ≤ ∑ _index : Fin n, (q : ℝ) * charge := by
      apply Finset.sum_le_sum
      intro index _member
      have castBound : ((occupied index).card : ℝ) ≤ q := by
        exact_mod_cast occupiedCard index
      convert mul_le_mul_of_nonneg_right castBound charge_nonnegative using 1 <;>
        dsimp only [charge] <;> ring
    _ = (n : ℝ) * ((q : ℝ) * charge) := by simp
    _ ≤ (a : ℝ) * ((q : ℝ) * charge) := by
      gcongr
    _ = (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
      dsimp only [charge]
      ring

/-- Causal-order theorem.  Every deterministic observation of the completed
profile—including any fixed adaptive reveal strategy—obeys the same bound. -/
theorem occupiedLinkProfile_observation_statDist_le
    {n : ℕ} {T : Type v} [Fintype T] [DecidableEq T]
    (occupied : Fin n → Finset C) (stored : Fin n → C → C)
    (observe : (Fin n → C × C) → T) :
    statDist
        (RandomSystems.Dist.fTransform observe
          (occupiedLinkProfileReal occupied stored))
        (RandomSystems.Dist.fTransform observe
          occupiedLinkProfileIdeal) ≤
      ∑ index,
        (occupied index).card * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
  exact (statDist_fTransform_le _ _ observe).trans
    (occupiedLinkProfile_statDist_le_closed occupied stored)

/-! ## History-dependent occupancy profiles

The fixed-profile theorem above is not, by itself, the causal statement used
by the simulator.  At the time an inner endpoint is activated, the set of
already occupied outer rows is a deterministic function of the preceding
graph history.  The following distributions keep that history as an explicit
first coordinate.  Because the same history law occurs on both sides, the
statistical distance is exactly the history-weighted average of the local
profile distances.  No independence assumption on the choice of the
occupancy profile is needed.
-/

variable {H : Type v} [Fintype H]

/-- A real occupied-link profile selected by a previously sampled history. -/
def dependentOccupiedLinkProfileReal {n : ℕ}
    (history : RandomSystems.Dist H)
    (occupied : H → Fin n → Finset C)
    (stored : H → Fin n → C → C) :
    RandomSystems.Dist (H × (Fin n → C × C)) :=
  RandomSystems.Dist.ofFiniteMassFunction fun sample =>
    history sample.1 *
      occupiedLinkProfileReal (occupied sample.1) (stored sample.1) sample.2

/-- The corresponding ideal profile, with the same history coordinate. -/
def dependentOccupiedLinkProfileIdeal {n : ℕ}
    (history : RandomSystems.Dist H) :
    RandomSystems.Dist (H × (Fin n → C × C)) :=
  RandomSystems.Dist.ofFiniteMassFunction fun sample =>
    history sample.1 * occupiedLinkProfileIdeal sample.2

@[simp]
theorem dependentOccupiedLinkProfileReal_apply {n : ℕ}
    (history : RandomSystems.Dist H)
    (occupied : H → Fin n → Finset C)
    (stored : H → Fin n → C → C)
    (sample : H × (Fin n → C × C)) :
    dependentOccupiedLinkProfileReal history occupied stored sample =
      history sample.1 *
        occupiedLinkProfileReal (occupied sample.1) (stored sample.1)
          sample.2 := by
  simp [dependentOccupiedLinkProfileReal]

@[simp]
theorem dependentOccupiedLinkProfileIdeal_apply {n : ℕ}
    (history : RandomSystems.Dist H)
    (sample : H × (Fin n → C × C)) :
    dependentOccupiedLinkProfileIdeal (C := C) history sample =
      history sample.1 * occupiedLinkProfileIdeal sample.2 := by
  simp [dependentOccupiedLinkProfileIdeal]

omit [Nonempty C] in
/-- The causal profile distance is the exact average of the fixed-history
distances.  This is the finite kernel-mixture identity needed by arbitrary
query interleavings. -/
theorem dependentOccupiedLinkProfile_statDist {n : ℕ}
    (history : RandomSystems.Dist H) (historyNonnegative : history.NonNeg)
    (occupied : H → Fin n → Finset C)
    (stored : H → Fin n → C → C) :
    statDist
        (dependentOccupiedLinkProfileReal history occupied stored)
        (dependentOccupiedLinkProfileIdeal history) =
      ∑ h : H, history h *
        statDist
          (occupiedLinkProfileReal (occupied h) (stored h))
          occupiedLinkProfileIdeal := by
  simp_rw [statDist_eq_sum_univ]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _member
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro values _member
  change
    max
      (history h * occupiedLinkProfileReal (occupied h) (stored h) values -
        history h * occupiedLinkProfileIdeal values) 0 =
      history h * max
        (occupiedLinkProfileReal (occupied h) (stored h) values -
          occupiedLinkProfileIdeal values) 0
  rw [← mul_sub, mul_max_of_nonneg _ _ (historyNonnegative h)]
  simp

/-- Uniform row and input budgets remain valid when the occupied sets are
chosen from the complete preceding history. -/
theorem dependentOccupiedLinkProfile_statDist_le_budget {n q a : ℕ}
    (history : RandomSystems.Dist H) (historyProbability : history.isProbDist)
    (occupied : H → Fin n → Finset C)
    (stored : H → Fin n → C → C)
    (occupiedCard : ∀ h index, (occupied h index).card ≤ q)
    (inputCard : n ≤ a) :
    statDist
        (dependentOccupiedLinkProfileReal history occupied stored)
        (dependentOccupiedLinkProfileIdeal history) ≤
      (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  let bound : ℝ := (q : ℝ) * (a : ℝ) *
    ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ) ^ 2
  rw [dependentOccupiedLinkProfile_statDist history
    historyProbability.nonNeg occupied stored]
  calc
    (∑ h : H, history h *
        statDist
          (occupiedLinkProfileReal (occupied h) (stored h))
          occupiedLinkProfileIdeal) ≤
        ∑ h : H, history h * bound := by
      apply Finset.sum_le_sum
      intro h _member
      exact mul_le_mul_of_nonneg_left
        (occupiedLinkProfile_statDist_le_budget
          (occupied h) (stored h) (occupiedCard h) inputCard)
        (historyProbability.nonNeg h)
    _ = bound * history.weight := by
      rw [← Finset.sum_mul]
      simp only [RandomSystems.Dist.weight_eq_sum]
      ring
    _ = bound := by rw [historyProbability.weight_eq, mul_one]
    _ = (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := rfl

/-- Every deterministic continuation/observation of a causal occupied-link
profile satisfies the same sharp budget. -/
theorem dependentOccupiedLinkProfile_observation_statDist_le_budget
    {n q a : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (history : RandomSystems.Dist H) (historyProbability : history.isProbDist)
    (occupied : H → Fin n → Finset C)
    (stored : H → Fin n → C → C)
    (occupiedCard : ∀ h index, (occupied h index).card ≤ q)
    (inputCard : n ≤ a)
    (observe : (H × (Fin n → C × C)) → T) :
    statDist
        (RandomSystems.Dist.fTransform observe
          (dependentOccupiedLinkProfileReal history occupied stored))
        (RandomSystems.Dist.fTransform observe
          (dependentOccupiedLinkProfileIdeal history)) ≤
      (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  exact (statDist_fTransform_le _ _ observe).trans
    (dependentOccupiedLinkProfile_statDist_le_budget history
      historyProbability occupied stored occupiedCard inputCard)

/-! ## Fully causal occupied-link products

The preceding dependent-profile theorem chooses an entire batch after one
shared history.  The simulator needs the stronger sequential statement:
round `i` may choose its occupied set and stored row values from the first `i`
link samples themselves.  `CausalOccupiedLinkProfile` records precisely that
dependency, and `RandomSystems.causalProduct_statDist_le_sum` performs the
hybrid argument without assuming independence between rounds.
-/

/-- Occupancy and stored answers chosen from the complete strict link history. -/
structure CausalOccupiedLinkProfile (C : Type u) where
  occupied : {i : ℕ} → (Fin i → C × C) → Finset C
  stored : {i : ℕ} → (Fin i → C × C) → C → C

/-- Real causal laws: at a given history, use the exact occupied-link law
selected by that history. -/
def causalOccupiedLinkRealLaws
    (profile : CausalOccupiedLinkProfile C) :
    RandomSystems.CausalLaws (C × C) where
  law := fun history =>
    occupiedLinkReal (profile.occupied history) (profile.stored history)

/-- Ideal causal laws: every newly activated link is an independent uniform
endpoint/answer pair. -/
def causalOccupiedLinkIdealLaws : RandomSystems.CausalLaws (C × C) where
  law := fun _history => occupiedLinkIdeal

/-- Completed real causal link transcript. -/
def causalOccupiedLinkReal
    (profile : CausalOccupiedLinkProfile C) (n : ℕ) :
    RandomSystems.Dist (Fin n → C × C) :=
  RandomSystems.causalProduct (causalOccupiedLinkRealLaws profile) n

/-- Completed ideal causal link transcript. -/
def causalOccupiedLinkIdeal (n : ℕ) :
    RandomSystems.Dist (Fin n → C × C) :=
  RandomSystems.causalProduct
    (causalOccupiedLinkIdealLaws (C := C)) n

theorem causalOccupiedLinkReal_isProbDist
    (profile : CausalOccupiedLinkProfile C) (n : ℕ) :
    (causalOccupiedLinkReal profile n).isProbDist := by
  exact RandomSystems.causalProduct_isProbDist _
    (fun history =>
      occupiedLinkReal_isProbDist
        (profile.occupied history) (profile.stored history)) n

theorem causalOccupiedLinkIdeal_isProbDist (n : ℕ) :
    (causalOccupiedLinkIdeal (C := C) n).isProbDist := by
  exact RandomSystems.causalProduct_isProbDist _
    (fun _history => occupiedLinkIdeal_isProbDist) n

/-- Sharp causal occupied-link budget.  The occupied rows at round `i` may be
an arbitrary function of all earlier endpoint/answer pairs. -/
theorem causalOccupiedLink_statDist_le_budget {n q a : ℕ}
    (profile : CausalOccupiedLinkProfile C)
    (occupiedCard : ∀ {i} (history : Fin i → C × C),
      (profile.occupied history).card ≤ q)
    (inputCard : n ≤ a) :
    statDist (causalOccupiedLinkReal profile n)
        (causalOccupiedLinkIdeal n) ≤
      (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  let charge : ℝ := ((Fintype.card C : ℝ) - 1) /
    (Fintype.card C : ℝ) ^ 2
  have chargeNonnegative : 0 ≤ charge := by
    exact occupied_row_charge_nonneg
  have causalBound := RandomSystems.causalProduct_statDist_le_sum
    (causalOccupiedLinkRealLaws profile)
    (causalOccupiedLinkIdealLaws (C := C))
    (fun history =>
      occupiedLinkReal_isProbDist
        (profile.occupied history) (profile.stored history))
    (fun _history => occupiedLinkIdeal_isProbDist)
    (fun _index => (q : ℝ) * charge)
    (fun history => by
      dsimp only [causalOccupiedLinkRealLaws,
        causalOccupiedLinkIdealLaws, charge]
      convert occupiedLink_statDist_le_of_card_le
          (profile.occupied history) (profile.stored history)
          (occupiedCard history) using 1 <;> ring) n
  calc
    statDist (causalOccupiedLinkReal profile n)
          (causalOccupiedLinkIdeal n) ≤
        ∑ index ∈ Finset.range n, (q : ℝ) * charge := causalBound
    _ = (n : ℝ) * ((q : ℝ) * charge) := by simp
    _ ≤ (a : ℝ) * ((q : ℝ) * charge) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast inputCard)
        (mul_nonneg (Nat.cast_nonneg q) chargeNonnegative)
    _ = (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
      dsimp only [charge]
      ring

/-- Data processing preserves the causal link budget for every deterministic
continuation of the completed link transcript. -/
theorem causalOccupiedLink_observation_statDist_le_budget
    {n q a : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (profile : CausalOccupiedLinkProfile C)
    (occupiedCard : ∀ {i} (history : Fin i → C × C),
      (profile.occupied history).card ≤ q)
    (inputCard : n ≤ a)
    (observe : (Fin n → C × C) → T) :
    statDist
        (RandomSystems.Dist.fTransform observe
          (causalOccupiedLinkReal profile n))
        (RandomSystems.Dist.fTransform observe
          (causalOccupiedLinkIdeal n)) ≤
      (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  exact (statDist_fTransform_le _ _ observe).trans
    (causalOccupiedLink_statDist_le_budget profile occupiedCard inputCard)

end MDSimulator
end RandomSystemsModel
end SequenceHash
