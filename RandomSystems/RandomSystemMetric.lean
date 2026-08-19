/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CompatibleMetric
import RandomSystems.RandomSystemQuotient

/-!
# The maximal-advantage metric on fixed-signature random systems

On normalized representatives, maximal distinguishing advantage is symmetric,
subadditive, and separates transcript-equivalence classes.  It therefore gives
the behavioral quotient an actual `MetricSpace`, not merely a pseudometric.
This construction is independent of representative-distance attainment and
optimal coupling.
-/

namespace RandomSystems.CR18

universe u v

variable {X : Type u} {Y : Type v}

/-- Zero maximal advantage between normalized representatives forces equality
of every transcript law. -/
theorem equivalent_of_maximal_advantage_eq_zero
    (S T : PFunPDS.Prob X Y)
    (h : maxAdvantage S.val T.val = 0) : Equivalent S.val T.val := by
  have hSnn : S.val.NonNeg := S.property.1
  have hTnn : T.val.NonNeg := T.property.1
  have hTS : Adv T.val S.val = 0 := by
    rw [adv_eq_maxAdvantage_swap hTnn hSnn, h]
  have hST : Adv S.val T.val = 0 := by
    rw [adv_eq_maxAdvantage_swap hSnn hTnn,
      maxAdvantage_comm T.property S.property, h]
  intro e n
  apply le_antisymm
  · apply (delta_eq_zero_iff_le (transcriptDist_nonNeg hTnn e n)).mp
    have hle_real :=
      (transcript_distance_le_optimal_advantage hSnn hTnn e n).trans_eq hST
    exact le_antisymm hle_real (δ_nonneg _ _)
  · apply (delta_eq_zero_iff_le (transcriptDist_nonNeg hSnn e n)).mp
    have hle_real :=
      (transcript_distance_le_optimal_advantage hTnn hSnn e n).trans_eq hTS
    exact le_antisymm hle_real (δ_nonneg _ _)

/-- On normalized PDSs, zero maximal advantage is exactly transcript
equivalence. -/
theorem maximal_advantage_eq_zero_iff_equivalent
    (S T : PFunPDS.Prob X Y) :
    maxAdvantage S.val T.val = 0 ↔ Equivalent S.val T.val :=
  ⟨equivalent_of_maximal_advantage_eq_zero S T,
    maximal_advantage_eq_zero_of_equivalent S.property.1 T.property.1⟩

namespace RandomSystem

/-- The operational maximal distinguishing advantage is the metric on the
fixed-signature behavioral quotient. -/
noncomputable instance instMetricSpace : MetricSpace (RandomSystem X Y) where
  dist := maximalAdvantage
  dist_self R := Quotient.inductionOn R fun S => maxAdvantage_self S.val
  dist_comm R S := Quotient.inductionOn₂ R S fun R S =>
    maxAdvantage_comm R.property S.property
  dist_triangle R S T := Quotient.inductionOn₃ R S T fun R S T =>
    maxAdvantage_triangle R.val S.val T.val
  eq_of_dist_eq_zero := by
    intro R S h
    induction R using Quotient.inductionOn with
    | _ R =>
      induction S using Quotient.inductionOn with
      | _ S =>
        apply Quotient.sound
        exact equivalent_of_maximal_advantage_eq_zero R S h

/-- Representative formula for the quotient metric. -/
@[simp]
theorem dist_of_prob (S T : PFunPDS.Prob X Y) :
    dist (ofProb S) (ofProb T) = maxAdvantage S.val T.val :=
  rfl

/-- The quotient distance vanishes exactly at equality. -/
theorem dist_eq_zero_iff (R S : RandomSystem X Y) :
    dist R S = 0 ↔ R = S :=
  dist_eq_zero

/-- Random-system distance is bounded by one. -/
theorem dist_le_one (R S : RandomSystem X Y) : dist R S ≤ 1 := by
  induction R using Quotient.inductionOn with
  | _ R =>
    induction S using Quotient.inductionOn with
    | _ S =>
      exact maxAdvantage_le_one R.property S.property

/-- Representative formula for extended distance. -/
@[simp]
theorem edist_of_prob (S T : PFunPDS.Prob X Y) :
    edist (ofProb S) (ofProb T) = ENNReal.ofReal (maxAdvantage S.val T.val) := by
  rw [edist_dist, dist_of_prob]

/-- Extended random-system distance is bounded by one. -/
theorem edist_le_one (R S : RandomSystem X Y) : edist R S ≤ 1 := by
  rw [edist_dist]
  simpa using ENNReal.ofReal_le_ofReal (dist_le_one R S)

end RandomSystem

end RandomSystems.CR18
