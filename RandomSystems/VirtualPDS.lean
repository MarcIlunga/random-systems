/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BoundedAttainment

/-!
# Signed, or virtual, representatives of random systems

`RandomSystems.Dist A` is already the finite real vector space `A →₀ ℝ`.
Non-negativity is a predicate, not part of that carrier, so no second virtual
distribution datatype is needed.  This module puts the normed proof layer on
that existing linear envelope.

The central accounting rule is to combine coefficients belonging to the same
atom before taking an absolute value.  Deterministic pushforward then contracts
the resulting `L1` norm.  Consequently, signed PDS representatives that have
the same transcript pushforwards as honest systems give sound upper bounds on
the ordinary distinguishing advantage, even though the representatives
themselves cannot be sampled or conditioned in general.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems

namespace Dist

variable {A B : Type*}

/-- The `L1` norm of a finitely supported real mass function.  This is defined
after equal atoms have already been combined by `Finsupp`. -/
def virtualL1 (μ : Dist A) : ℝ :=
  μ.sum fun _ w => |w|

/-- Half the `L1` distance between two possibly signed finite laws. -/
def virtualDistance (μ ν : Dist A) : ℝ :=
  (1 / 2 : ℝ) * virtualL1 (μ - ν)

/-- A signed density relative to the uniform law, represented as a finite real
mass function. -/
def ofUniformDensity (A : Type*) [Fintype A] (f : A → ℝ) : Dist A :=
  ofFiniteMassFunction fun a => f a / (Fintype.card A : ℝ)

/-- The positive variation of a signed finite law. -/
def positiveVariation (μ : Dist A) : ℝ :=
  μ.sum fun _ w => max w 0

theorem virtualL1_nonneg (μ : Dist A) : 0 ≤ virtualL1 μ := by
  unfold virtualL1
  exact Finsupp.sum_nonneg fun _ _ => abs_nonneg _

theorem virtualDistance_nonneg (μ ν : Dist A) :
    0 ≤ virtualDistance μ ν := by
  exact mul_nonneg (by norm_num) (virtualL1_nonneg (μ - ν))

theorem weight_ofUniformDensity [Fintype A] (f : A → ℝ) :
    (ofUniformDensity A f).weight =
      (∑ a : A, f a) / (Fintype.card A : ℝ) := by
  rw [ofUniformDensity, weight_ofFiniteMassFunction]
  simpa using
    (Finset.sum_div (s := Finset.univ) (f := f)
      (a := (Fintype.card A : ℝ))).symm

theorem virtualL1_ofUniformDensity [Fintype A] (f : A → ℝ) :
    virtualL1 (ofUniformDensity A f) =
      (∑ a : A, |f a|) / (Fintype.card A : ℝ) := by
  unfold virtualL1
  rw [Finsupp.sum_fintype _ _ (by simp)]
  have hcard : 0 ≤ (Fintype.card A : ℝ) := by positivity
  simp only [ofUniformDensity, ofFiniteMassFunction_apply, abs_div,
    abs_of_nonneg hcard]
  simpa using
    (Finset.sum_div (s := Finset.univ) (f := fun a : A => |f a|)
      (a := (Fintype.card A : ℝ))).symm

theorem virtualDistance_ofUniformDensity_zero [Fintype A] (f : A → ℝ) :
    virtualDistance (ofUniformDensity A f) 0 =
      (1 / 2 : ℝ) *
        ((∑ a : A, |f a|) / (Fintype.card A : ℝ)) := by
  rw [virtualDistance, sub_zero, virtualL1_ofUniformDensity]

theorem weight_sub (μ ν : Dist A) :
    (μ - ν).weight = μ.weight - ν.weight := by
  unfold weight
  exact Finsupp.sum_sub_index fun _ _ _ => rfl

theorem weight_add (μ ν : Dist A) :
    (μ + ν).weight = μ.weight + ν.weight := by
  unfold weight
  exact Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

@[simp]
theorem ofUniformDensity_add [Fintype A] (f g : A → ℝ) :
    ofUniformDensity A (fun a => f a + g a) =
      ofUniformDensity A f + ofUniformDensity A g := by
  ext a
  simp [ofUniformDensity, add_div]

/-- The elementary Jordan identity for a finite signed law. -/
theorem virtualL1_eq_two_mul_positiveVariation_sub_weight (μ : Dist A) :
    virtualL1 μ = 2 * positiveVariation μ - μ.weight := by
  have hpoint (x : ℝ) : |x| = 2 * max x 0 - x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx', max_eq_right hx']
      ring
  unfold virtualL1 positiveVariation weight
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum]
  calc
    (∑ a ∈ μ.support, |μ a|) =
        ∑ a ∈ μ.support, (2 * max (μ a) 0 - μ a) := by
          exact Finset.sum_congr rfl fun a _ => hpoint (μ a)
    _ = 2 * (∑ a ∈ μ.support, max (μ a) 0) -
          ∑ a ∈ μ.support, μ a := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- A zero-weight signed law has half-`L1` norm equal to its positive
variation. -/
theorem virtualDistance_zero_eq_positiveVariation {μ : Dist A}
    (hweight : μ.weight = 0) :
    (1 / 2 : ℝ) * virtualL1 μ = positiveVariation μ := by
  rw [virtualL1_eq_two_mul_positiveVariation_sub_weight, hweight]
  ring

/-- For a non-negative second law, the positive variation of `μ - ν` is the
repository's one-sided statistical distance `δ μ ν`. -/
theorem positiveVariation_sub_eq_delta (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) :
    positiveVariation (μ - ν) = CR18.δ μ ν := by
  classical
  let U := μ.support ∪ ν.support
  have hsub : (μ - ν).support ⊆ U := by
    simpa [U, sub_eq_add_neg, Finsupp.support_neg] using
      (Finsupp.support_add (g₁ := μ) (g₂ := -ν))
  have hμsub : μ.support ⊆ U := by
    exact Finset.subset_union_left
  calc
    positiveVariation (μ - ν) =
        ∑ a ∈ U, max ((μ - ν) a) 0 := by
          exact Finsupp.sum_of_support_subset (μ - ν) hsub
            (fun _ w => max w 0) (by simp)
    _ = ∑ a ∈ U, max (μ a - ν a) 0 := by
          simp only [Finsupp.sub_apply]
    _ = CR18.δ μ ν := by
          symm
          unfold CR18.δ
          exact Finsupp.sum_of_support_subset μ hμsub
            (fun a w => max (w - ν a) 0) (by
              intro a _ha
              dsimp
              rw [zero_sub, max_eq_right (neg_nonpos.mpr (hν a))])

/-- On equal-weight laws, when the second law is honest, virtual distance is
exactly ordinary statistical distance.  The first law need not be positive. -/
theorem virtualDistance_eq_delta_of_eq_weight (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) (hweight : μ.weight = ν.weight) :
    virtualDistance μ ν = CR18.δ μ ν := by
  unfold virtualDistance
  rw [virtualDistance_zero_eq_positiveVariation]
  · exact positiveVariation_sub_eq_delta μ hν
  · rw [weight_sub, hweight, sub_self]

@[simp]
theorem fTransform_sub (f : A → B) (μ ν : Dist A) :
    fTransform f (μ - ν) = fTransform f μ - fTransform f ν := by
  exact Finsupp.mapDomain_sub

/-- Fiberwise cancellation can only decrease the signed `L1` norm. -/
theorem virtualL1_fTransform_le (f : A → B) (μ : Dist A) :
    virtualL1 (fTransform f μ) ≤ virtualL1 μ := by
  classical
  unfold virtualL1
  rw [Finsupp.sum, Finsupp.sum]
  have hsub : (fTransform f μ).support ⊆ μ.support.image f :=
    Finsupp.mapDomain_support
  rw [Finset.sum_subset hsub]
  · rw [← Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image_of_mem f ha) (fun a => |μ a|)]
    apply Finset.sum_le_sum
    intro b hb
    rw [fTransform_apply_eq_mass, mass, Finsupp.sum, ← Finset.sum_filter]
    exact Finset.abs_sum_le_sum_abs _ _
  · intro b _hb hnot
    rw [Finsupp.notMem_support_iff.mp hnot, abs_zero]

/-- Deterministic post-processing contracts virtual distance. -/
theorem virtualDistance_fTransform_le (f : A → B) (μ ν : Dist A) :
    virtualDistance (fTransform f μ) (fTransform f ν) ≤
      virtualDistance μ ν := by
  rw [virtualDistance, virtualDistance, ← fTransform_sub]
  exact mul_le_mul_of_nonneg_left (virtualL1_fTransform_le f (μ - ν)) (by norm_num)

end Dist

namespace CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-- A virtual PDS is the raw, already-signed PDS carrier.  Honest systems are
the elements satisfying `Dist.NonNeg`; normalized honest systems are
`PFunPDS.Prob`. -/
abbrev VirtualPDS (X : Type u) (Y : Type v) := PFunPDS X Y

/-- Virtual equivalence is ordinary observational equivalence: every
deterministic environment sees the same transcript pushforward.  Positivity is
irrelevant to this linear equality. -/
abbrev VirtuallyEquivalent (S T : VirtualPDS X Y) : Prop := Equivalent S T

/-- The static cost of two virtual PDS representatives. -/
def virtualPDSDistance (S T : VirtualPDS X Y) : ℝ :=
  Dist.virtualDistance S T

/-- Distance between observational classes when all finite signed
representatives are allowed. -/
def virtualClassDistance (S T : PFunPDS X Y) : ℝ :=
  sInf {a : ℝ | ∃ S' T' : VirtualPDS X Y,
    Equivalent S' S ∧ Equivalent T' T ∧
      a = virtualPDSDistance S' T'}

/-- A signed representative certificate cannot understate operational
distinguishing advantage.  The representatives `S'` and `T'` may have negative
coefficients; only their observable transcript laws, inherited from the honest
equal-weight source systems, need to be non-negative.

This is the signed extension of Lanzenberger--Maurer's data-processing
direction. -/
theorem advantage_le_virtualPDSDistance_of_equivalent
    {S T S' T' : PFunPDS X Y}
    (_hS : S.NonNeg) (hT : T.NonNeg) (hweight : S.weight = T.weight)
    (hS' : Equivalent S' S) (hT' : Equivalent T' T) :
    Adv S T ≤ virtualPDSDistance S' T' := by
  unfold Adv
  refine csSup_le ⟨_, ⟨(fun _ => none), 0, rfl⟩⟩ ?_
  · rintro a ⟨e, n, rfl⟩
    rw [← hS' e n, ← hT' e n]
    have hT'transcript : (transcriptDist T' e n).NonNeg := by
      rw [hT' e n]
      exact transcriptDist_nonNeg hT e n
    have htranscriptWeight :
        (transcriptDist S' e n).weight =
          (transcriptDist T' e n).weight := by
      rw [transcriptDist, transcriptDist,
        Dist.weight_fTransform, Dist.weight_fTransform,
        weight_eq_of_equivalent hS', weight_eq_of_equivalent hT', hweight]
    calc
      CR18.δ (transcriptDist S' e n) (transcriptDist T' e n) =
          Dist.virtualDistance (transcriptDist S' e n)
            (transcriptDist T' e n) :=
        (Dist.virtualDistance_eq_delta_of_eq_weight
          (transcriptDist S' e n) hT'transcript htranscriptWeight).symm
      _ ≤ Dist.virtualDistance S' T' := by
        unfold transcriptDist
        exact Dist.virtualDistance_fTransform_le
          (fun s => PFunDDS.transcript s e n) S' T'

/-- Probability-system specialization of the signed certificate theorem. -/
theorem advantage_le_virtualPDSDistance_of_prob_equivalent
    (S T : PFunPDS.Prob X Y) (S' T' : VirtualPDS X Y)
    (hS' : Equivalent S' S.val) (hT' : Equivalent T' T.val) :
    Adv S.val T.val ≤ virtualPDSDistance S' T' := by
  exact advantage_le_virtualPDSDistance_of_equivalent
    S.property.nonNeg T.property.nonNeg
    (S.property.weight_eq.trans T.property.weight_eq.symm) hS' hT'

/-- Allowing arbitrary signed representatives still cannot lower the class
distance below operational advantage. -/
theorem advantage_le_virtualClassDistance
    {S T : PFunPDS X Y} (hS : S.NonNeg) (hT : T.NonNeg)
    (hweight : S.weight = T.weight) :
    Adv S T ≤ virtualClassDistance S T := by
  unfold virtualClassDistance
  refine le_csInf ?_ ?_
  · exact ⟨virtualPDSDistance S T, S, T,
      (fun _ _ => rfl), (fun _ _ => rfl), rfl⟩
  · rintro a ⟨S', T', hS', hT', rfl⟩
    exact advantage_le_virtualPDSDistance_of_equivalent
      hS hT hweight hS' hT'

/-- The signed class distance is attained as soon as an honest equivalent pair
attains `Adv`.  This isolates the purely linear signed argument from the
common-domain induction that constructs the honest pair. -/
theorem virtualClassDistance_eq_advantage_of_exists_honest_attainment
    {S T : PFunPDS X Y} (hS : S.NonNeg) (hT : T.NonNeg)
    (hweight : S.weight = T.weight)
    (hattain : ∃ S' T' : PFunPDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' S ∧ Equivalent T' T ∧
      CR18.δ S' T' = Adv S T) :
    virtualClassDistance S T = Adv S T := by
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', hdelta⟩ := hattain
  have hrepresentativeWeight : S'.weight = T'.weight := by
    rw [weight_eq_of_equivalent hS', weight_eq_of_equivalent hT', hweight]
  have hcost : virtualPDSDistance S' T' = Adv S T := by
    rw [virtualPDSDistance,
      Dist.virtualDistance_eq_delta_of_eq_weight S' hT'nn hrepresentativeWeight,
      hdelta]
  apply le_antisymm
  · unfold virtualClassDistance
    rw [← hcost]
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro a ⟨R, U, _hR, _hU, rfl⟩
      exact Dist.virtualDistance_nonneg R U
    · exact ⟨S', T', hS', hT', rfl⟩
  · exact advantage_le_virtualClassDistance hS hT hweight

/-- For the exact finite/common-domain/bounded source class, allowing signed
representatives is sound and already attains the operational advantage.  No
extra attainment assumption remains: the honest representatives constructed
by the source induction witness the signed infimum. -/
theorem virtualClassDistance_eq_advantage_of_finite_common_domain_and_bounded
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)} {q : Nat}
    (hS : S.NonNeg) (hT : T.NonNeg) (hweight : S.weight = T.weight)
    (hbounded : PFunPDS.HaveCommonDomainAndBounded S T D q) :
    virtualClassDistance S T = Adv S T := by
  apply virtualClassDistance_eq_advantage_of_exists_honest_attainment
    hS hT hweight
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', _hSw, _hTw, hdelta⟩ :=
    exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded
      hS hT hbounded
  exact ⟨S', T', hS'nn, hT'nn, hS', hT', hdelta⟩

/-- Bundled probability-system form of exact virtual-class attainment. -/
theorem virtualClassDistance_eq_advantage_of_prob_finite_common_domain_and_bounded
    [Fintype X] (S T : PFunPDS.Prob X Y) {D : Set (List X)} {q : Nat}
    (hbounded : PFunPDS.HaveCommonDomainAndBounded S.val T.val D q) :
    virtualClassDistance S.val T.val = Adv S.val T.val := by
  exact virtualClassDistance_eq_advantage_of_finite_common_domain_and_bounded
    S.property.nonNeg T.property.nonNeg
    (S.property.weight_eq.trans T.property.weight_eq.symm) hbounded

end CR18

end RandomSystems
