import RandomSystems.StatDist

/-!
# The exact occupied-link replacement

This module formalizes the finite calculation behind the causal link step of
the SequenceHash simulator.  `occupiedLinkReal` is the real joint law of a
hidden inner endpoint and its outer answer after some terminal sites have
already been exposed.  `occupiedLinkIdeal` makes the endpoint and answer
independent and uniform.

The main result, `occupiedLink_statDist`, is exact: every occupied row loses
precisely `(N - 1) / N^2` of common mass.  It is independent of the stored
answers and is therefore suitable for the later adaptive/common-carrier lift.
-/

noncomputable section

open scoped BigOperators

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- The real joint mass of hidden endpoint `z` and visible answer `y`.
An occupied row is concentrated on its already stored answer; an unoccupied
row is uniform. -/
def occupiedLinkRealMass (occupied : Finset C) (stored : C → C)
    (zy : C × C) : ℝ :=
  if zy.1 ∈ occupied then
    if zy.2 = stored zy.1 then
      1 / (Fintype.card C : ℝ)
    else
      0
  else
    1 / (Fintype.card C : ℝ) ^ 2

/-- The independent ideal joint mass of hidden endpoint and ideal answer. -/
def occupiedLinkIdealMass (_zy : C × C) : ℝ :=
  1 / (Fintype.card C : ℝ) ^ 2

def occupiedLinkReal (occupied : Finset C) (stored : C → C) :
    Dist (C × C) :=
  Dist.ofFiniteMassFunction (occupiedLinkRealMass occupied stored)

def occupiedLinkIdeal : Dist (C × C) :=
  Dist.ofFiniteMassFunction occupiedLinkIdealMass

/-- The maximal common carrier of the real and ideal link laws.  This is the
pointwise minimum from Lanzenberger--Maurer's common-part construction, made
public here because the generic development currently keeps it private. -/
def occupiedLinkCommon (occupied : Finset C) (stored : C → C) :
    Dist (C × C) :=
  Dist.ofFiniteMassFunction fun zy =>
    min (occupiedLinkReal occupied stored zy)
      (occupiedLinkIdeal (C := C) zy)

/-- The real mass discarded by the common carrier. -/
def occupiedLinkRealResidual (occupied : Finset C) (stored : C → C) :
    Dist (C × C) :=
  occupiedLinkReal occupied stored - occupiedLinkCommon occupied stored

/-- The ideal mass discarded by the same common carrier. -/
def occupiedLinkIdealResidual (occupied : Finset C) (stored : C → C) :
    Dist (C × C) :=
  occupiedLinkIdeal - occupiedLinkCommon occupied stored

@[simp]
theorem occupiedLinkCommon_apply (occupied : Finset C) (stored : C → C)
    (zy : C × C) :
    occupiedLinkCommon occupied stored zy =
      min (occupiedLinkReal occupied stored zy)
        (occupiedLinkIdeal (C := C) zy) := by
  simp [occupiedLinkCommon]

@[simp]
theorem occupiedLinkRealResidual_apply (occupied : Finset C)
    (stored : C → C) (zy : C × C) :
    occupiedLinkRealResidual occupied stored zy =
      occupiedLinkReal occupied stored zy -
        occupiedLinkCommon occupied stored zy := by
  rfl

@[simp]
theorem occupiedLinkIdealResidual_apply (occupied : Finset C)
    (stored : C → C) (zy : C × C) :
    occupiedLinkIdealResidual occupied stored zy =
      occupiedLinkIdeal zy - occupiedLinkCommon occupied stored zy := by
  rfl

theorem occupiedLinkCommon_le_real (occupied : Finset C) (stored : C → C)
    (zy : C × C) :
    occupiedLinkCommon occupied stored zy ≤
      occupiedLinkReal occupied stored zy := by
  rw [occupiedLinkCommon_apply]
  exact min_le_left _ _

theorem occupiedLinkCommon_le_ideal (occupied : Finset C) (stored : C → C)
    (zy : C × C) :
    occupiedLinkCommon occupied stored zy ≤ occupiedLinkIdeal zy := by
  rw [occupiedLinkCommon_apply]
  exact min_le_right _ _

theorem sub_min_eq_max_sub (left right : ℝ) :
    left - min left right = max (left - right) 0 := by
  rcases le_total left right with hle | hle
  · rw [min_eq_left hle, sub_self,
      max_eq_right (sub_nonpos.mpr hle)]
  · rw [min_eq_right hle, max_eq_left (sub_nonneg.mpr hle)]

/-- The real residual is exactly the pointwise positive excess used by
statistical distance. -/
theorem occupiedLinkRealResidual_eq_positivePart (occupied : Finset C)
    (stored : C → C) (zy : C × C) :
    occupiedLinkRealResidual occupied stored zy =
      max (occupiedLinkReal occupied stored zy - occupiedLinkIdeal zy) 0 := by
  rw [occupiedLinkRealResidual_apply, occupiedLinkCommon_apply,
    sub_min_eq_max_sub]

/-- The ideal residual is the reverse pointwise positive excess. -/
theorem occupiedLinkIdealResidual_eq_positivePart (occupied : Finset C)
    (stored : C → C) (zy : C × C) :
    occupiedLinkIdealResidual occupied stored zy =
      max (occupiedLinkIdeal zy - occupiedLinkReal occupied stored zy) 0 := by
  rw [occupiedLinkIdealResidual_apply, occupiedLinkCommon_apply, min_comm,
    sub_min_eq_max_sub]

/-- The common carrier and real residual reconstruct the real law exactly. -/
theorem occupiedLinkCommon_add_realResidual (occupied : Finset C)
    (stored : C → C) :
    occupiedLinkCommon occupied stored +
        occupiedLinkRealResidual occupied stored =
      occupiedLinkReal occupied stored := by
  ext zy
  simp only [Finsupp.add_apply, occupiedLinkRealResidual_apply]
  ring

/-- The same common carrier and ideal residual reconstruct the ideal law. -/
theorem occupiedLinkCommon_add_idealResidual (occupied : Finset C)
    (stored : C → C) :
    occupiedLinkCommon occupied stored +
        occupiedLinkIdealResidual occupied stored =
      occupiedLinkIdeal := by
  ext zy
  simp only [Finsupp.add_apply, occupiedLinkIdealResidual_apply]
  ring

/-- The independent ideal law is literally uniform on the product carrier. -/
theorem occupiedLinkIdeal_eq_uniform :
    occupiedLinkIdeal (C := C) = Dist.uniform (C × C) := by
  ext zy
  simp [occupiedLinkIdeal, occupiedLinkIdealMass, Dist.uniform_apply,
    Fintype.card_prod]
  ring

omit [DecidableEq C] in
theorem card_real_pos : (0 : ℝ) < (Fintype.card C : ℝ) := by
  exact_mod_cast Fintype.card_pos

omit [DecidableEq C] in
theorem occupied_row_charge_nonneg :
    (0 : ℝ) ≤ ((Fintype.card C : ℝ) - 1) /
      (Fintype.card C : ℝ) ^ 2 := by
  have hcard : (1 : ℝ) ≤ (Fintype.card C : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact div_nonneg (sub_nonneg.mpr hcard) (sq_nonneg _)

/-- Every hidden-endpoint row has mass `1/N`, including occupied rows. -/
theorem occupiedLinkReal_row_sum (occupied : Finset C) (stored : C → C)
    (z : C) :
    (∑ y : C, occupiedLinkReal occupied stored (z, y)) =
      1 / (Fintype.card C : ℝ) := by
  have hcard : (Fintype.card C : ℝ) ≠ 0 := ne_of_gt card_real_pos
  by_cases hz : z ∈ occupied
  · simp [occupiedLinkReal, occupiedLinkRealMass, hz]
  · simp only [occupiedLinkReal, Dist.ofFiniteMassFunction_apply,
      occupiedLinkRealMass, hz, if_false,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- Every row of the independent ideal law also has mass `1/N`. -/
theorem occupiedLinkIdeal_row_sum (z : C) :
    (∑ y : C, occupiedLinkIdeal (z, y)) =
      1 / (Fintype.card C : ℝ) := by
  have hcard : (Fintype.card C : ℝ) ≠ 0 := ne_of_gt card_real_pos
  simp only [occupiedLinkIdeal, Dist.ofFiniteMassFunction_apply,
    occupiedLinkIdealMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The hidden endpoint is exactly uniform in the real occupied-link law. -/
theorem occupiedLinkReal_fst (occupied : Finset C) (stored : C → C) :
    Dist.fTransform Prod.fst (occupiedLinkReal occupied stored) =
      Dist.uniform C := by
  ext z
  rw [Dist.fTransform_apply_eq_mass, Dist.mass_eq_sum]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · simpa [Dist.uniform_apply] using
      occupiedLinkReal_row_sum occupied stored z
  · intro z' _hz' hne
    simp [hne]
  · simp

/-- The hidden endpoint is exactly uniform in the independent ideal law. -/
theorem occupiedLinkIdeal_fst :
    Dist.fTransform Prod.fst (occupiedLinkIdeal (C := C)) =
      Dist.uniform C := by
  ext z
  rw [Dist.fTransform_apply_eq_mass, Dist.mass_eq_sum]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · simpa [Dist.uniform_apply] using occupiedLinkIdeal_row_sum (C := C) z
  · intro z' _hz' hne
    simp [hne]
  · simp

/-- The visible answer is exactly uniform in the independent ideal law. -/
theorem occupiedLinkIdeal_snd :
    Dist.fTransform Prod.snd (occupiedLinkIdeal (C := C)) =
      Dist.uniform C := by
  rw [occupiedLinkIdeal_eq_uniform]
  exact Dist.fTransform_snd_uniform C C

/-- The real occupied-link mass function is an honest probability law. -/
theorem occupiedLinkReal_isProbDist (occupied : Finset C) (stored : C → C) :
    (occupiedLinkReal occupied stored).isProbDist := by
  constructor
  · intro zy
    by_cases hz : zy.1 ∈ occupied <;>
      by_cases hy : zy.2 = stored zy.1 <;>
      simp [occupiedLinkReal, occupiedLinkRealMass, hz, hy]
  · rw [occupiedLinkReal, Dist.weight_ofFiniteMassFunction,
      Fintype.sum_prod_type]
    change (∑ z : C, ∑ y : C, occupiedLinkReal occupied stored (z, y)) = 1
    simp_rw [occupiedLinkReal_row_sum]
    simpa using (Dist.weight_uniform (A := C))

/-- The independent ideal mass function is an honest probability law. -/
theorem occupiedLinkIdeal_isProbDist :
    (occupiedLinkIdeal (C := C)).isProbDist := by
  constructor
  · intro zy
    simp [occupiedLinkIdeal, occupiedLinkIdealMass]
  · rw [occupiedLinkIdeal, Dist.weight_ofFiniteMassFunction,
      Fintype.sum_prod_type]
    change (∑ z : C, ∑ y : C, occupiedLinkIdeal (z, y)) = 1
    simp_rw [occupiedLinkIdeal_row_sum]
    simpa using (Dist.weight_uniform (A := C))

/-- The maximal common carrier is an honest subdistribution. -/
theorem occupiedLinkCommon_nonNeg (occupied : Finset C) (stored : C → C) :
    (occupiedLinkCommon occupied stored).NonNeg := by
  intro zy
  rw [occupiedLinkCommon_apply]
  exact le_min
    ((occupiedLinkReal_isProbDist occupied stored).nonNeg zy)
    (occupiedLinkIdeal_isProbDist.nonNeg zy)

/-- The real excess over the common carrier is nonnegative. -/
theorem occupiedLinkRealResidual_nonNeg (occupied : Finset C)
    (stored : C → C) :
    (occupiedLinkRealResidual occupied stored).NonNeg := by
  intro zy
  rw [occupiedLinkRealResidual_apply]
  exact sub_nonneg.mpr (occupiedLinkCommon_le_real occupied stored zy)

/-- The ideal excess over the common carrier is nonnegative. -/
theorem occupiedLinkIdealResidual_nonNeg (occupied : Finset C)
    (stored : C → C) :
    (occupiedLinkIdealResidual occupied stored).NonNeg := by
  intro zy
  rw [occupiedLinkIdealResidual_apply]
  exact sub_nonneg.mpr (occupiedLinkCommon_le_ideal occupied stored zy)

/-- Pointwise positive excess.  Lean checks all three semantic cases:
unoccupied row, occupied matching answer, and occupied nonmatching answer. -/
theorem occupiedLink_positive_part (occupied : Finset C) (stored : C → C)
    (z y : C) :
    max (occupiedLinkReal occupied stored (z, y) -
        occupiedLinkIdeal (z, y)) 0 =
      if z ∈ occupied ∧ y = stored z then
        ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ) ^ 2
      else
        0 := by
  have hcard : (Fintype.card C : ℝ) ≠ 0 := ne_of_gt card_real_pos
  by_cases hz : z ∈ occupied
  · by_cases hy : y = stored z
    · rw [if_pos ⟨hz, hy⟩]
      simp only [occupiedLinkReal, occupiedLinkIdeal,
        Dist.ofFiniteMassFunction_apply, occupiedLinkRealMass,
        occupiedLinkIdealMass, hz, hy, if_pos]
      have heq :
          1 / (Fintype.card C : ℝ) - 1 / (Fintype.card C : ℝ) ^ 2 =
            ((Fintype.card C : ℝ) - 1) /
              (Fintype.card C : ℝ) ^ 2 := by
        field_simp
      rw [heq, max_eq_left occupied_row_charge_nonneg]
    · rw [if_neg (fun h => hy h.2)]
      simp only [occupiedLinkReal, occupiedLinkIdeal,
        Dist.ofFiniteMassFunction_apply, occupiedLinkRealMass,
        occupiedLinkIdealMass, hz, hy, if_pos, if_false]
      apply max_eq_right
      have hsquare : (0 : ℝ) ≤ 1 / (Fintype.card C : ℝ) ^ 2 := by
        positivity
      linarith
  · rw [if_neg (fun h => hz h.1)]
    simp [occupiedLinkReal, occupiedLinkIdeal, occupiedLinkRealMass,
      occupiedLinkIdealMass, hz]

/-- Exact distance of the occupied-link replacement. -/
theorem occupiedLink_statDist (occupied : Finset C) (stored : C → C) :
    statDist (occupiedLinkReal occupied stored) occupiedLinkIdeal =
      (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  rw [statDist_eq_sum_univ, Fintype.sum_prod_type]
  simp_rw [occupiedLink_positive_part]
  have hrow : ∀ z : C,
      (∑ y : C,
        if z ∈ occupied ∧ y = stored z then
          ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ) ^ 2
        else 0) =
      if z ∈ occupied then
        ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ) ^ 2
      else 0 := by
    intro z
    by_cases hz : z ∈ occupied
    · simp [hz]
    · simp [hz]
  simp_rw [hrow]
  rw [Finset.sum_ite]
  simp
  ring

/-- The real residual's total weight is exactly the link distance. -/
theorem occupiedLinkRealResidual_weight (occupied : Finset C)
    (stored : C → C) :
    (occupiedLinkRealResidual occupied stored).weight =
      statDist (occupiedLinkReal occupied stored) occupiedLinkIdeal := by
  rw [Dist.weight_eq_sum, statDist_eq_sum_univ]
  exact Finset.sum_congr rfl fun zy _ =>
    occupiedLinkRealResidual_eq_positivePart occupied stored zy

/-- The ideal residual's total weight is the reverse statistical distance. -/
theorem occupiedLinkIdealResidual_weight_reverse (occupied : Finset C)
    (stored : C → C) :
    (occupiedLinkIdealResidual occupied stored).weight =
      statDist occupiedLinkIdeal (occupiedLinkReal occupied stored) := by
  rw [Dist.weight_eq_sum, statDist_eq_sum_univ]
  exact Finset.sum_congr rfl fun zy _ =>
    occupiedLinkIdealResidual_eq_positivePart occupied stored zy

/-- Because both link laws have weight one, both residuals have the same
weight.  Thus the discarded mass is a single bad-event charge, not two. -/
theorem occupiedLinkIdealResidual_weight (occupied : Finset C)
    (stored : C → C) :
    (occupiedLinkIdealResidual occupied stored).weight =
      statDist (occupiedLinkReal occupied stored) occupiedLinkIdeal := by
  rw [occupiedLinkIdealResidual_weight_reverse,
    statDist_symm_of_eq_weight]
  rw [(occupiedLinkReal_isProbDist occupied stored).weight_eq,
    occupiedLinkIdeal_isProbDist.weight_eq]

/-- The retained common-carrier mass is one minus the exact discarded mass. -/
theorem occupiedLinkCommon_weight (occupied : Finset C) (stored : C → C) :
    (occupiedLinkCommon occupied stored).weight =
      1 - statDist (occupiedLinkReal occupied stored) occupiedLinkIdeal := by
  calc
    (occupiedLinkCommon occupied stored).weight =
        ∑ zy : C × C, occupiedLinkCommon occupied stored zy :=
      Dist.weight_eq_sum _
    _ = ∑ zy : C × C,
          (occupiedLinkReal occupied stored zy -
            occupiedLinkRealResidual occupied stored zy) := by
      apply Finset.sum_congr rfl
      intro zy _member
      rw [occupiedLinkRealResidual_apply]
      ring
    _ = (∑ zy : C × C, occupiedLinkReal occupied stored zy) -
          ∑ zy : C × C, occupiedLinkRealResidual occupied stored zy :=
      by rw [Finset.sum_sub_distrib]
    _ = (occupiedLinkReal occupied stored).weight -
          (occupiedLinkRealResidual occupied stored).weight := by
      rw [Dist.weight_eq_sum, Dist.weight_eq_sum]
    _ = 1 - statDist (occupiedLinkReal occupied stored) occupiedLinkIdeal := by
      rw [(occupiedLinkReal_isProbDist occupied stored).weight_eq,
        occupiedLinkRealResidual_weight]

/-- Closed form for the retained mass. -/
theorem occupiedLinkCommon_weight_closed (occupied : Finset C)
    (stored : C → C) :
    (occupiedLinkCommon occupied stored).weight =
      1 - (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  rw [occupiedLinkCommon_weight, occupiedLink_statDist]

/-- A row-count bound immediately bounds one occupied-link replacement. -/
theorem occupiedLink_statDist_le_of_card_le (occupied : Finset C)
    (stored : C → C) {q : ℕ} (card_le : occupied.card ≤ q) :
    statDist (occupiedLinkReal occupied stored) occupiedLinkIdeal ≤
      (q : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  rw [occupiedLink_statDist]
  have hcharge :
      (0 : ℝ) ≤ ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := occupied_row_charge_nonneg
  have hcast : (occupied.card : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast card_le
  have hmul := mul_le_mul_of_nonneg_right hcast hcharge
  simpa [mul_div_assoc] using hmul

/-- Static multi-input link accounting.  This is the finite sum consumed by
the later causal hybrid: at most `q` occupied rows for each of at most `a`
activated construction inputs gives the exact `q*a*(N-1)/N^2` envelope. -/
theorem sum_occupiedLink_statDist_le
    {X : Type*} [Fintype X] [DecidableEq X]
    (inputs : Finset X) (occupied : X → Finset C)
    (stored : X → C → C) {q a : ℕ}
    (input_card_le : inputs.card ≤ a)
    (occupied_card_le : ∀ input ∈ inputs, (occupied input).card ≤ q) :
    (∑ input ∈ inputs,
      statDist (occupiedLinkReal (occupied input) (stored input))
        occupiedLinkIdeal) ≤
      (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  let charge : ℝ := ((Fintype.card C : ℝ) - 1) /
    (Fintype.card C : ℝ) ^ 2
  have hcharge : 0 ≤ charge := occupied_row_charge_nonneg
  calc
    (∑ input ∈ inputs,
        statDist (occupiedLinkReal (occupied input) (stored input))
          occupiedLinkIdeal)
        ≤ ∑ _input ∈ inputs, (q : ℝ) * charge := by
          exact Finset.sum_le_sum fun input hinput => by
            convert occupiedLink_statDist_le_of_card_le
              (occupied input) (stored input) (occupied_card_le input hinput)
                using 1 <;> dsimp [charge] <;> ring
    _ = (inputs.card : ℝ) * ((q : ℝ) * charge) := by
          simp
    _ ≤ (a : ℝ) * ((q : ℝ) * charge) := by
          gcongr
    _ = (q : ℝ) * (a : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
          dsimp [charge]
          ring

end MDSimulator
end RandomSystemsModel
end SequenceHash
