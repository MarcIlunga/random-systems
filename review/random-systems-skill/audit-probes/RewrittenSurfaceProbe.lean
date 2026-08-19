import RandomSystems.SwitchingLemma
import RandomSystems.HTechnique.Derivation
import RandomSystems.RandomSystemCoupling
import RandomSystems.StrictContextSharedDomain
import RandomSystems.QueryCompression

#check RandomSystems.CR18.CondEquiv.CondEquiv
#check RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le
#check RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good
#check RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_ratio_of_good
#check RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_expectation
#check RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_partition
#check RandomSystems.probBad_iUnion_le
#check RandomSystems.CR18.mass_biUnion_le
#check RandomSystems.CR18.HTechniqueDerivation.probBad_le_of_ratio
#check RandomSystems.CR18.pairCollisionUnionBound_le_birthday
#check RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress
#check RandomSystems.CR18.compressedQuery_bound
#check RandomSystems.CR18.optimal_probability_coupling_exists
#check RandomSystems.CR18.StrictContextAdvantage.maxEDist_le_maxAdvantage
#check RandomSystems.CR18.StrictContextSharedDomain.maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain
#check RandomSystems.CR18.adv_eq_maxAdvantage_swap

open RandomSystems.CR18
open scoped RandomSystems.CR18.HTechniqueDerivation

example {X Y : Type} {q : ℕ} [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) (Bad : TranscriptPrefix X Y q → Prop) (δb : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_good : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      ¬ Bad t → (tr(S, xs)) t = (tr(T, xs)) t)
    (h_bad : ∀ E : QQueryEnvironment X Y q,
      Pr[Bad ∣ tr[q](T, E.1)] ≤ δb) :
    Adv[q](S, T) ≤ (δb : ℝ) := by
  exact RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good
    S T Bad δb hS hT h_good h_bad
