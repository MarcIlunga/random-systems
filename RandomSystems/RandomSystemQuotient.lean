/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem
import RandomSystems.SemanticRegistry

/-!
# Fixed-signature random systems

A public random system of signature `(X,Y)` is a probability distribution over
partial deterministic systems, quotiented by equality of every observable
transcript law.  The quotient relation is `Equivalent`; the successful-answer
kernel is deliberately not used for partial systems.

The maximal distinguishing advantage descends directly to this quotient.  No
attained representative or coupling theorem is needed: representative
independence follows by rewriting transcript laws.  The metric structure is
installed downstream in `RandomSystems.RandomSystemMetric`, after the
probability-level symmetry and triangle theorems are available.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

namespace PFunPDS

/-- A point mass at one deterministic system is a normalized probabilistic
system. -/
theorem pure_is_probability_distribution (s : PFunDDS.DDS X Y) :
    (pure s).isProbDist :=
  Dist.isProbDist_single s

/-- The normalized point mass at one deterministic system. -/
noncomputable def pureProb (s : PFunDDS.DDS X Y) : Prob X Y :=
  ⟨pure s, pure_is_probability_distribution s⟩

/-- The normalized point mass exposes the expected underlying law. -/
@[simp]
theorem pure_prob_coe_eq_pure (s : PFunDDS.DDS X Y) :
    (pureProb s).val = pure s :=
  rfl

end PFunPDS

/-- One-sided finite-support statistical distance vanishes exactly when the
first distribution is pointwise dominated by the second.  The `NonNeg` side
condition on the second law is Def 2.4 content over the signed carrier: off
the first law's support `δ` cannot see a negative `nu`. -/
theorem delta_eq_zero_iff_le {A : Type*} {mu nu : Dist A} (hnu : nu.NonNeg) :
    δ mu nu = 0 ↔ mu ≤ nu := by
  constructor
  · intro h
    rw [Finsupp.le_def]
    intro a
    by_cases ha : a ∈ mu.support
    · unfold δ at h
      rw [Finsupp.sum] at h
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => le_max_right (mu b - nu b) 0)).mp h a ha
      exact sub_nonpos.mp (max_eq_right_iff.mp hterm)
    · rw [Finsupp.notMem_support_iff.mp ha]
      exact hnu a
  · intro h
    unfold δ
    rw [Finsupp.sum]
    exact Finset.sum_eq_zero fun a _ =>
      max_eq_right (sub_nonpos.mpr (Finsupp.le_def.mp h a))

/-- Transcript equivalence is reflexive. -/
theorem equivalent_refl (S : PFunPDS X Y) : Equivalent S S :=
  fun _ _ => rfl

/-- Transcript equivalence is symmetric. -/
theorem equivalent_symm {S T : PFunPDS X Y} (h : Equivalent S T) :
    Equivalent T S :=
  fun e n => (h e n).symm

/-- Transcript equivalence is transitive. -/
theorem equivalent_trans {S T U : PFunPDS X Y}
    (hST : Equivalent S T) (hTU : Equivalent T U) : Equivalent S U :=
  fun e n => (hST e n).trans (hTU e n)

/-- The canonical setoid on normalized PDS representatives. -/
def PFunPDS.Prob.equivalentSetoid (X : Type u) (Y : Type v) :
    Setoid (PFunPDS.Prob X Y) where
  r S T := Equivalent S.val T.val
  iseqv := ⟨
    fun S => equivalent_refl S.val,
    fun h => equivalent_symm h,
    fun hST hTU => equivalent_trans hST hTU⟩

/-- A normalized random system with one fixed input/output signature. -/
def RandomSystem (X : Type u) (Y : Type v) : Type (max u v) :=
  Quotient (PFunPDS.Prob.equivalentSetoid X Y)

/-- Every finite-prefix transcript distance is bounded by the optimal
transcript distinguishing advantage. -/
theorem transcript_distance_le_optimal_advantage
    {S T : PFunPDS X Y} (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (e : PFunDDS.DDE X Y) (n : Nat) :
    δ (transcriptDist S e n) (transcriptDist T e n) ≤ Adv S T :=
  le_csSup (bddAbove_adv_set hSnn hTnn) ⟨e, n, rfl⟩

/-- Replacing either representative by a transcript-equivalent PDS leaves the
optimal transcript advantage unchanged. -/
theorem optimal_advantage_eq_of_equivalent
    {S S' T T' : PFunPDS X Y}
    (hS : Equivalent S S') (hT : Equivalent T T') :
    Adv S T = Adv S' T' := by
  unfold Adv
  congr 1
  ext a
  constructor
  · rintro ⟨e, n, rfl⟩
    exact ⟨e, n, by rw [hS e n, hT e n]⟩
  · rintro ⟨e, n, rfl⟩
    exact ⟨e, n, by rw [← hS e n, ← hT e n]⟩

/-- Replacing either representative by a transcript-equivalent PDS leaves the
classical maximal distinguishing advantage unchanged. -/
theorem maximal_advantage_eq_of_equivalent
    {S S' T T' : PFunPDS X Y}
    (hSnn : S.NonNeg) (hS'nn : S'.NonNeg)
    (hTnn : T.NonNeg) (hT'nn : T'.NonNeg)
    (hS : Equivalent S S') (hT : Equivalent T T') :
    maxAdvantage S T = maxAdvantage S' T' := by
  rw [← adv_eq_maxAdvantage_swap hTnn hSnn,
    ← adv_eq_maxAdvantage_swap hT'nn hS'nn]
  exact optimal_advantage_eq_of_equivalent hT hS

/-- Transcript-equivalent representatives have zero maximal distinguishing
advantage. -/
theorem maximal_advantage_eq_zero_of_equivalent
    {S T : PFunPDS X Y} (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : Equivalent S T) :
    maxAdvantage S T = 0 := by
  rw [← adv_eq_maxAdvantage_swap hTnn hSnn]
  exact adv_eq_zero_of_equivalent (equivalent_symm h)

namespace RandomSystem

/-- Insert a normalized PDS representative into its behavioral quotient. -/
@[rs_rule "rs.system.of_probability" rs_system random_systems]
def ofProb (S : PFunPDS.Prob X Y) : RandomSystem X Y :=
  Quotient.mk (PFunPDS.Prob.equivalentSetoid X Y) S

/-- Equality of displayed representatives is exactly transcript equivalence. -/
theorem of_prob_eq_of_prob_iff (S T : PFunPDS.Prob X Y) :
    ofProb S = ofProb T ↔ Equivalent S.val T.val := by
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    exact h

/-- Equality of displayed representatives is exactly cumulative observable
behavior equality through the CR18 `s ↦ s⊥` view. -/
theorem of_prob_eq_of_prob_iff_observable_behavior_equivalent
    (S T : PFunPDS.Prob X Y) :
    ofProb S = ofProb T ↔ ObservableBehaviorEq S.val T.val := by
  rw [of_prob_eq_of_prob_iff]
  exact (behavior_equivalent_iff_transcript_equivalent S T).symm

/-- Maximal distinguishing advantage on the behavioral quotient. -/
noncomputable def maximalAdvantage
    (R S : RandomSystem X Y) : Real :=
  Quotient.liftOn₂ R S
    (fun R S => maxAdvantage R.val S.val)
    (fun Ra Sa Rb Sb hR hS =>
      maximal_advantage_eq_of_equivalent Ra.property.1 Rb.property.1
        Sa.property.1 Sb.property.1 hR hS)

/-- The quotient advantage agrees definitionally with representative
advantage. -/
@[simp]
theorem maximal_advantage_of_prob (S T : PFunPDS.Prob X Y) :
    maximalAdvantage (ofProb S) (ofProb T) = maxAdvantage S.val T.val :=
  rfl

end RandomSystem

end RandomSystems.CR18
