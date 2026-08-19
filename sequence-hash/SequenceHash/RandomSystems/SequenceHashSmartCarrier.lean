import SequenceHash.RandomSystems.SequenceHashSmartTrace

/-!
# The finite common carrier for the SequenceHash simulator

The real representative is first enlarged by an unused ideal-oracle table.
This puts the real and ideal systems on the same uniform product carrier.  A
fixed public history then selects a finite permutation of that carrier by the
terminal exchanges proved in `SequenceHashSmartTrace`.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems
open RandomSystems.CR18

universe u

variable {C B X Tag : Type u}

/-- The correlated real representative with an unused independent oracle
coordinate.  The augmentation changes neither the system law nor its weight. -/
def augmentedRealP [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    PFunPDS (Query C B X) (Reply C B X) :=
  Dist.fTransform
    (fun seed : Coins C B X =>
      PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv
          (correlatedAugmentedCoins grammar iv seed)))
    (Dist.uniform (Coins C B X))

/-- Adding the unused uniform oracle coordinate is an exact representative
change: the augmented law is the ordinary real SequenceHash law. -/
theorem augmentedRealP_eq_realP [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    augmentedRealP grammar iv = (realP grammar iv).val := by
  rw [real_p_eq_historyEvaluator grammar iv]
  unfold augmentedRealP
  let observeCompression : Compression C B →
      PFunDDS.DDS (Query C B X) (Reply C B X) :=
    fun compression =>
      PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv
          (correlatedCoins grammar iv compression))
  have dropDummy :
      Dist.fTransform
          (fun seed : Coins C B X =>
            observeCompression (compressionOfTable seed.2))
          (Dist.uniform (Coins C B X)) =
        Dist.fTransform
          (fun table : C × B → C =>
            observeCompression (compressionOfTable table))
          (Dist.uniform (C × B → C)) := by
    rw [← Dist.prod_uniform]
    exact Dist.fTransform_map_snd_prod_uniform (X → C) (C × B → C)
      (fun table : C × B → C =>
        observeCompression (compressionOfTable table))
  rw [show
      (fun seed : Coins C B X =>
        PFunDDS.historyEvaluator
          (simulatorHistoryOutput grammar iv
            (correlatedAugmentedCoins grammar iv seed))) =
        (fun seed : Coins C B X =>
          observeCompression (compressionOfTable seed.2)) by
      rfl]
  rw [dropDummy]
  have curryUniform :
      Dist.fTransform (Equiv.curry C B C)
          (Dist.uniform (C × B → C)) =
        Dist.uniform (Compression C B) :=
    Dist.fTransform_equiv_uniform (Equiv.curry C B C)
  rw [← curryUniform, Dist.fTransform_comp]
  rfl

/-- The ideal history system is already carried by the same uniform product
seed used by `augmentedRealP`. -/
def augmentedIdealP [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    PFunPDS (Query C B X) (Reply C B X) :=
  Dist.fTransform
    (fun seed : Coins C B X =>
      PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv seed))
    (Dist.uniform (Coins C B X))

theorem augmentedIdealP_eq_idealP [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    augmentedIdealP grammar iv = (idealP grammar iv).val := by
  exact (ideal_p_eq_historyEvaluator grammar iv).symm

/-- On the retained branch, the fixed-history real observation equals the
ideal observation after applying the revealed terminal permutation. -/
theorem augmentedReal_output_eq_ideal_after_smartSwap
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (seed : Coins C B X) (history : List (Query C B X))
    (nonempty : history ≠ [])
    (terminalsDistinct : SmartTerminalsDistinct grammar iv
      (compressionOfTable seed.2) history)
    (linkConsistent : SmartLinkConsistent grammar iv
      (compressionOfTable seed.2) history seed.1) :
    simulatorHistoryOutput grammar iv
        (correlatedAugmentedCoins grammar iv seed) history nonempty =
      simulatorHistoryOutput grammar iv
        (smartSwapCoins grammar iv (compressionOfTable seed.2) history seed)
        history nonempty :=
  simulatorHistoryOutput_correlatedAugmented_eq_smartSwap grammar iv seed
    history nonempty terminalsDistinct linkConsistent

/-- The fixed-history exchange controls every prefix of the retained history,
not just its final answer.  This is the form required by an adaptive
environment: all earlier answers agree, so it makes the same later queries. -/
theorem augmentedReal_output_eq_ideal_after_smartSwap_of_prefix
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (seed : Coins C B X) (history : List (Query C B X))
    {front : List (Query C B X)} (isPrefix : front <+: history)
    (nonempty : front ≠ [])
    (terminalsDistinct : SmartTerminalsDistinct grammar iv
      (compressionOfTable seed.2) history)
    (linkConsistent : SmartLinkConsistent grammar iv
      (compressionOfTable seed.2) history seed.1) :
    simulatorHistoryOutput grammar iv
        (correlatedAugmentedCoins grammar iv seed) front nonempty =
      simulatorHistoryOutput grammar iv
        (smartSwapCoins grammar iv (compressionOfTable seed.2) history seed)
        front nonempty := by
  have safeFull := replaySafe_correlatedAugmented_smartSwap grammar iv seed
    history terminalsDistinct linkConsistent
  have safePrefix : ReplaySafe grammar iv
      (correlatedAugmentedCoins grammar iv seed)
      (smartSwapCoins grammar iv (compressionOfTable seed.2) history seed)
      front := by
    exact replaySafeFrom_prefix grammar iv _ _ (initialState iv) isPrefix
      safeFull
  exact simulatorHistoryOutput_eq_of_replaySafe grammar iv _ _ front
    nonempty safePrefix

/-! ## Adaptive transcript selected by the real execution -/

/-- The public query history generated by a deterministic environment against
one augmented-real seed. -/
def augmentedRealQueryHistory [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X) : List (Query C B X) :=
  PFunDDS.transcriptInputs
    (PFunDDS.transcript
      (PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv
          (correlatedAugmentedCoins grammar iv seed)))
      environment rounds)

/-- Apply the smart terminal exchange selected by the query history that the
same seed actually generates in the real execution. -/
def adaptiveSmartMatch [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X) : Coins C B X :=
  smartSwapCoins grammar iv (compressionOfTable seed.2)
    (augmentedRealQueryHistory grammar iv environment rounds seed) seed

/-- Exact adaptive replay under the history-selected terminal exchange.  The
only premises are the two mathematical good-history conditions; no
nonadaptivity or fixed-query assumption is present. -/
theorem augmentedReal_transcript_eq_ideal_adaptiveSmartMatch
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X)
    (terminalsDistinct : SmartTerminalsDistinct grammar iv
      (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed))
    (linkConsistent : SmartLinkConsistent grammar iv
      (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) seed.1) :
    PFunDDS.transcript
        (PFunDDS.historyEvaluator
          (simulatorHistoryOutput grammar iv
            (correlatedAugmentedCoins grammar iv seed)))
        environment rounds =
      PFunDDS.transcript
        (PFunDDS.historyEvaluator
          (simulatorHistoryOutput grammar iv
            (adaptiveSmartMatch grammar iv environment rounds seed)))
        environment rounds := by
  apply transcript_historyEvaluator_eq_of_prefix_agree
  intro front nonempty isPrefix
  exact augmentedReal_output_eq_ideal_after_smartSwap_of_prefix grammar iv
    seed (augmentedRealQueryHistory grammar iv environment rounds seed)
    isPrefix nonempty terminalsDistinct linkConsistent

/-! ## Recoverable adaptive matchings -/

/-- A target-side schedule extractor certifies recoverability when it returns
exactly the terminal-pair list used by the source-side adaptive exchange.  The
extractor may inspect the whole matched seed; the graph argument will later
instantiate it with the uniquely decoded good execution. -/
def AdaptiveSmartRecoverable [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B)))
    (seed : Coins C B X) : Prop :=
  recoverPairs (adaptiveSmartMatch grammar iv environment rounds seed) =
    smartFreePairs grammar iv (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed)

/-- Undo the coordinate exchange named by a target-side schedule extractor. -/
def adaptiveSmartRecover [DecidableEq C] [DecidableEq B]
    [DecidableEq X]
    (recoverPairs : Coins C B X → List (X × (C × B)))
    (target : Coins C B X) : Coins C B X :=
  (RandomSystems.coordinateSwaps (recoverPairs target)).symm target

theorem adaptiveSmartRecover_match [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B)))
    (seed : Coins C B X)
    (recoverable : AdaptiveSmartRecoverable grammar iv environment rounds
      recoverPairs seed) :
    adaptiveSmartRecover recoverPairs
        (adaptiveSmartMatch grammar iv environment rounds seed) = seed := by
  unfold adaptiveSmartRecover
  rw [recoverable]
  unfold adaptiveSmartMatch smartSwapCoins
  exact Equiv.symm_apply_apply _ _

/-- The complete retained event for the adaptive partial matching.  The first
two fields prove transcript replay; the third makes the history-selected map
an injective partial matching. -/
def AdaptiveSmartGood [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B)))
    (seed : Coins C B X) : Prop :=
  SmartTerminalsDistinct grammar iv (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) ∧
    SmartLinkConsistent grammar iv (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) seed.1 ∧
    AdaptiveSmartRecoverable grammar iv environment rounds recoverPairs seed

theorem adaptiveSmartMatch_injOn_good [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B))) :
    Set.InjOn (adaptiveSmartMatch grammar iv environment rounds)
      {seed | AdaptiveSmartGood grammar iv environment rounds recoverPairs seed} := by
  intro left leftGood right rightGood equal
  have recovered := congrArg (adaptiveSmartRecover recoverPairs) equal
  rw [adaptiveSmartRecover_match grammar iv environment rounds recoverPairs
        left leftGood.2.2,
    adaptiveSmartRecover_match grammar iv environment rounds recoverPairs
        right rightGood.2.2] at recovered
  exact recovered

/-- Per-environment transcript distance is bounded by the exact complement of
the recoverable replay event.  This is a genuine adaptive coupling: the
history-selected injection is extended to a permutation of the finite seed
space, and the second marginal is therefore still the uniform ideal seed. -/
theorem augmentedTranscriptDist_le_adaptiveSmartBadMass
    [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B))) :
    δ
        (transcriptDist (augmentedRealP grammar iv)
          environment rounds)
        (transcriptDist (augmentedIdealP grammar iv)
          environment rounds) ≤
      (Dist.uniform (Coins C B X)).mass
        (fun seed =>
          ¬ AdaptiveSmartGood grammar iv environment rounds recoverPairs seed) := by
  classical
  let realObserve : Coins C B X →
      List (Query C B X × Option (Reply C B X)) := fun seed =>
    PFunDDS.transcript
      (PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv
          (correlatedAugmentedCoins grammar iv seed))) environment rounds
  let idealObserve : Coins C B X →
      List (Query C B X × Option (Reply C B X)) := fun seed =>
    PFunDDS.transcript
      (PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv seed)) environment rounds
  let good : Coins C B X → Prop :=
    AdaptiveSmartGood grammar iv environment rounds recoverPairs
  have matchInjective : Set.InjOn
      (adaptiveSmartMatch grammar iv environment rounds) {seed | good seed} :=
    adaptiveSmartMatch_injOn_good grammar iv environment rounds recoverPairs
  let permutation : Equiv.Perm (Coins C B X) :=
    RandomSystems.extendInjOnToPerm
      (adaptiveSmartMatch grammar iv environment rounds) good matchInjective
  let joint : RandomSystems.Dist (Coins C B X × Coins C B X) :=
    Dist.fTransform (fun seed => (seed, permutation seed))
      (Dist.uniform (Coins C B X))
  have jointNonnegative : joint.NonNeg :=
    Dist.uniform_nonNeg.fTransform _
  have firstMarginal : Dist.fTransform Prod.fst joint =
      Dist.uniform (Coins C B X) := by
    unfold joint
    rw [Dist.fTransform_comp]
    change Dist.fTransform id (Dist.uniform (Coins C B X)) = _
    exact Dist.fTransform_id _
  have secondMarginal : Dist.fTransform Prod.snd joint =
      Dist.uniform (Coins C B X) := by
    unfold joint
    rw [Dist.fTransform_comp]
    exact Dist.fTransform_equiv_uniform permutation
  have couplingBound :=
    HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne
      realObserve idealObserve jointNonnegative firstMarginal secondMarginal
  have disagreementBound :
      joint.mass (fun pair =>
          realObserve pair.1 ≠ idealObserve pair.2) ≤
        (Dist.uniform (Coins C B X)).mass (fun seed => ¬ good seed) := by
    unfold joint
    rw [Dist.mass_fTransform]
    apply Dist.mass_mono Dist.uniform_nonNeg
    intro seed mismatch seedGood
    apply mismatch
    have permutationGood : permutation seed =
        adaptiveSmartMatch grammar iv environment rounds seed :=
      RandomSystems.extendInjOnToPerm_apply_of_good
        (adaptiveSmartMatch grammar iv environment rounds) good matchInjective
        seed seedGood
    rw [permutationGood]
    exact augmentedReal_transcript_eq_ideal_adaptiveSmartMatch grammar iv
      environment rounds seed seedGood.1 seedGood.2.1
  unfold transcriptDist augmentedRealP augmentedIdealP
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  change δ (Dist.fTransform realObserve (Dist.uniform (Coins C B X)))
      (Dist.fTransform idealObserve (Dist.uniform (Coins C B X))) ≤ _
  exact couplingBound.trans disagreementBound

/-! ## Target-oriented recoverable adaptive matchings -/

/-- Retained event phrased on an ideal/target seed.  Recovering a source seed
must make the smart exchange return to the target, and that recovered source
must satisfy the two replay conditions.  This orientation is useful when the
graph bad event is simplest to count in the ideal simulator experiment. -/
def AdaptiveSmartTargetGood [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B)))
    (target : Coins C B X) : Prop :=
  let source := adaptiveSmartRecover recoverPairs target
  SmartTerminalsDistinct grammar iv (compressionOfTable source.2)
      (augmentedRealQueryHistory grammar iv environment rounds source) ∧
    SmartLinkConsistent grammar iv (compressionOfTable source.2)
      (augmentedRealQueryHistory grammar iv environment rounds source)
      source.1 ∧
    adaptiveSmartMatch grammar iv environment rounds source = target

/-- A right inverse is injective on its retained target domain. -/
theorem adaptiveSmartRecover_injOn_targetGood
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B))) :
    Set.InjOn (adaptiveSmartRecover recoverPairs)
      {target |
        AdaptiveSmartTargetGood grammar iv environment rounds recoverPairs
          target} := by
  intro left leftGood right rightGood recoveredEqual
  change
    SmartTerminalsDistinct grammar iv
        (compressionOfTable (adaptiveSmartRecover recoverPairs left).2)
        (augmentedRealQueryHistory grammar iv environment rounds
          (adaptiveSmartRecover recoverPairs left)) ∧
      SmartLinkConsistent grammar iv
        (compressionOfTable (adaptiveSmartRecover recoverPairs left).2)
        (augmentedRealQueryHistory grammar iv environment rounds
          (adaptiveSmartRecover recoverPairs left))
        (adaptiveSmartRecover recoverPairs left).1 ∧
      adaptiveSmartMatch grammar iv environment rounds
          (adaptiveSmartRecover recoverPairs left) = left at leftGood
  change
    SmartTerminalsDistinct grammar iv
        (compressionOfTable (adaptiveSmartRecover recoverPairs right).2)
        (augmentedRealQueryHistory grammar iv environment rounds
          (adaptiveSmartRecover recoverPairs right)) ∧
      SmartLinkConsistent grammar iv
        (compressionOfTable (adaptiveSmartRecover recoverPairs right).2)
        (augmentedRealQueryHistory grammar iv environment rounds
          (adaptiveSmartRecover recoverPairs right))
        (adaptiveSmartRecover recoverPairs right).1 ∧
      adaptiveSmartMatch grammar iv environment rounds
          (adaptiveSmartRecover recoverPairs right) = right at rightGood
  calc
    left = adaptiveSmartMatch grammar iv environment rounds
        (adaptiveSmartRecover recoverPairs left) := leftGood.2.2.symm
    _ = adaptiveSmartMatch grammar iv environment rounds
        (adaptiveSmartRecover recoverPairs right) := congrArg _ recoveredEqual
    _ = right := rightGood.2.2

/-- Target-oriented adaptive transcript coupling.  The recovered partial
inverse is extended to a permutation, so the real marginal remains exactly
uniform while the failure probability is measured on the ideal seed. -/
theorem augmentedTranscriptDist_le_adaptiveSmartTargetBadMass
    [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ)
    (recoverPairs : Coins C B X → List (X × (C × B))) :
    δ
        (transcriptDist (augmentedRealP grammar iv)
          environment rounds)
        (transcriptDist (augmentedIdealP grammar iv)
          environment rounds) ≤
      (Dist.uniform (Coins C B X)).mass
        (fun target =>
          ¬ AdaptiveSmartTargetGood grammar iv environment rounds
            recoverPairs target) := by
  classical
  let realObserve : Coins C B X →
      List (Query C B X × Option (Reply C B X)) := fun seed =>
    PFunDDS.transcript
      (PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv
          (correlatedAugmentedCoins grammar iv seed))) environment rounds
  let idealObserve : Coins C B X →
      List (Query C B X × Option (Reply C B X)) := fun seed =>
    PFunDDS.transcript
      (PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv seed)) environment rounds
  let recover : Coins C B X → Coins C B X :=
    adaptiveSmartRecover recoverPairs
  let good : Coins C B X → Prop :=
    AdaptiveSmartTargetGood grammar iv environment rounds recoverPairs
  have recoverInjective : Set.InjOn recover {target | good target} :=
    adaptiveSmartRecover_injOn_targetGood grammar iv environment rounds
      recoverPairs
  let permutation : Equiv.Perm (Coins C B X) :=
    RandomSystems.extendInjOnToPerm recover good recoverInjective
  let joint : RandomSystems.Dist (Coins C B X × Coins C B X) :=
    Dist.fTransform (fun target => (permutation target, target))
      (Dist.uniform (Coins C B X))
  have jointNonnegative : joint.NonNeg :=
    Dist.uniform_nonNeg.fTransform _
  have firstMarginal : Dist.fTransform Prod.fst joint =
      Dist.uniform (Coins C B X) := by
    unfold joint
    rw [Dist.fTransform_comp]
    exact Dist.fTransform_equiv_uniform permutation
  have secondMarginal : Dist.fTransform Prod.snd joint =
      Dist.uniform (Coins C B X) := by
    unfold joint
    rw [Dist.fTransform_comp]
    change Dist.fTransform id (Dist.uniform (Coins C B X)) = _
    exact Dist.fTransform_id _
  have couplingBound :=
    HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne
      realObserve idealObserve jointNonnegative firstMarginal secondMarginal
  have disagreementBound :
      joint.mass (fun pair =>
          realObserve pair.1 ≠ idealObserve pair.2) ≤
        (Dist.uniform (Coins C B X)).mass (fun target => ¬ good target) := by
    unfold joint
    rw [Dist.mass_fTransform]
    apply Dist.mass_mono Dist.uniform_nonNeg
    intro target mismatch targetGood
    apply mismatch
    have permutationGood : permutation target = recover target :=
      RandomSystems.extendInjOnToPerm_apply_of_good recover good
        recoverInjective target targetGood
    rw [permutationGood]
    change
      SmartTerminalsDistinct grammar iv
          (compressionOfTable (recover target).2)
          (augmentedRealQueryHistory grammar iv environment rounds
            (recover target)) ∧
        SmartLinkConsistent grammar iv
          (compressionOfTable (recover target).2)
          (augmentedRealQueryHistory grammar iv environment rounds
            (recover target))
          (recover target).1 ∧
        adaptiveSmartMatch grammar iv environment rounds (recover target) =
          target at targetGood
    have replay :=
      augmentedReal_transcript_eq_ideal_adaptiveSmartMatch grammar iv
        environment rounds (recover target) targetGood.1 targetGood.2.1
    exact replay.trans (congrArg idealObserve targetGood.2.2)
  unfold transcriptDist augmentedRealP augmentedIdealP
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  change δ (Dist.fTransform realObserve (Dist.uniform (Coins C B X)))
      (Dist.fTransform idealObserve (Dist.uniform (Coins C B X))) ≤ _
  exact couplingBound.trans disagreementBound

/-! ## Canonical recovery from the matched ideal execution -/

/-- Query history generated by one independent ideal/simulator seed. -/
def augmentedIdealQueryHistory [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X) : List (Query C B X) :=
  PFunDDS.transcriptInputs
    (PFunDDS.transcript
      (PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv seed)) environment rounds)

/-- The ideal execution itself reconstructs the terminal-pair schedule: rerun
the finite activation audit on its public query history and compression tape. -/
def canonicalAdaptiveRecoverPairs [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (target : Coins C B X) : List (X × (C × B)) :=
  smartFreePairs grammar iv (compressionOfTable target.2)
    (augmentedIdealQueryHistory grammar iv environment rounds target)

/-- The coordinate schedule is stable when rerunning the audit on the
exchanged compression tape but the same public query history produces the
same terminal pairs.  The graph-isolation proof discharges exactly this
condition. -/
def AdaptiveSmartScheduleStable [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X) : Prop :=
  smartFreePairs grammar iv
      (compressionOfTable
        (adaptiveSmartMatch grammar iv environment rounds seed).2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) =
    smartFreePairs grammar iv (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed)

theorem adaptiveSmartRecoverable_canonical_of_scheduleStable
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X)
    (terminalsDistinct : SmartTerminalsDistinct grammar iv
      (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed))
    (linkConsistent : SmartLinkConsistent grammar iv
      (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) seed.1)
    (scheduleStable : AdaptiveSmartScheduleStable grammar iv environment
      rounds seed) :
    AdaptiveSmartRecoverable grammar iv environment rounds
      (canonicalAdaptiveRecoverPairs grammar iv environment rounds) seed := by
  have transcriptEqual :=
    augmentedReal_transcript_eq_ideal_adaptiveSmartMatch grammar iv
      environment rounds seed terminalsDistinct linkConsistent
  have historyEqual := congrArg PFunDDS.transcriptInputs transcriptEqual
  unfold AdaptiveSmartRecoverable canonicalAdaptiveRecoverPairs
    augmentedIdealQueryHistory
  rw [← historyEqual]
  exact scheduleStable

/-- Canonical graph/link good event used by the end-to-end coupling. -/
def CanonicalAdaptiveSmartGood [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X) : Prop :=
  SmartTerminalsDistinct grammar iv (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) ∧
    SmartLinkConsistent grammar iv (compressionOfTable seed.2)
      (augmentedRealQueryHistory grammar iv environment rounds seed) seed.1 ∧
    AdaptiveSmartScheduleStable grammar iv environment rounds seed

/-- The canonical recoverability event follows from graph/link goodness. -/
theorem canonicalAdaptiveSmartGood_implies_good
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) (seed : Coins C B X)
    (good : CanonicalAdaptiveSmartGood grammar iv environment rounds seed) :
    AdaptiveSmartGood grammar iv environment rounds
      (canonicalAdaptiveRecoverPairs grammar iv environment rounds) seed := by
  exact ⟨good.1, good.2.1,
    adaptiveSmartRecoverable_canonical_of_scheduleStable grammar iv
      environment rounds seed good.1 good.2.1 good.2.2⟩

/-- Canonical adaptive transcript bound.  All representative/coupling
plumbing is now closed; the remaining application work is solely to bound the
three explicit bad branches in `CanonicalAdaptiveSmartGood`. -/
theorem augmentedTranscriptDist_le_canonicalSmartBadMass
    [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) :
    δ
        (transcriptDist (augmentedRealP grammar iv) environment rounds)
        (transcriptDist (augmentedIdealP grammar iv) environment rounds) ≤
      (Dist.uniform (Coins C B X)).mass
        (fun seed =>
          ¬ CanonicalAdaptiveSmartGood grammar iv environment rounds seed) := by
  let recoverPairs :=
    canonicalAdaptiveRecoverPairs grammar iv environment rounds
  have base := augmentedTranscriptDist_le_adaptiveSmartBadMass grammar iv
    environment rounds recoverPairs
  refine base.trans ?_
  apply Dist.mass_mono Dist.uniform_nonNeg
  intro seed notGeneral canonicalGood
  exact notGeneral
    (canonicalAdaptiveSmartGood_implies_good grammar iv environment rounds seed
      canonicalGood)

end MDSimulator
end RandomSystemsModel
end SequenceHash
