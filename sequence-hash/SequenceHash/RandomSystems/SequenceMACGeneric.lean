import SequenceHash.RandomSystems.SequenceMACGenericFiberMass

/-!
# SequenceMAC generic ideal-compression bound

This module places the R4 structural theorem on the filter-first random-systems
surface.  The history predicate below filters the `PFunPDS` domain before the
H-technique bridge is applied.  The two remaining deep obligations are exposed
as the named hypotheses `h_norm` and `h_badmass`.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems
open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique.IdealCompression

universe uBlock

/-! ## History-level tagged budget -/

/--
The domain-level form of `SequenceFunctionTaggedBudgetRespects`: at most `p`
direct compression queries, at most `q` construction evaluations, and the
canonical SequenceFunction cost of every visible evaluation is at most
`lambda`.
-/
def budgetHist {Block : Type uBlock} {L : U128} {users : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (p q lambda : ℕ) :
    List (SequenceFunctionICQuery Block L users) → Prop :=
  fun l =>
    let queries : List.Vector (SequenceFunctionICQuery Block L users) l.length :=
      ⟨l, rfl⟩
    primCount queries ≤ p ∧ evalCount queries ≤ q ∧
      ∀ e, TaggedQuery.eval e ∈ l →
        sequenceFunctionEvalCost model b S e ≤ lambda

/-- The domain-level SequenceFunction budget is closed under list prefixes. -/
theorem budgetHist_prefixClosed {Block : Type uBlock} {L : U128} {users : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (p q lambda : ℕ) :
    PrefixClosed (budgetHist (users := users) model b S p q lambda) := by
  classical
  intro l₁ l₂ hprefix hbudget
  simp only [budgetHist] at hbudget
  refine ⟨?_, ?_, ?_⟩
  · exact (primCount_le_of_toList_prefix _ _ (by simpa using hprefix)).trans hbudget.1
  · exact (evalCount_le_of_toList_prefix _ _ (by simpa using hprefix)).trans hbudget.2.1
  · intro e he
    exact hbudget.2.2 e (hprefix.subset he)

/-- Every admitted SequenceFunction history has at most `p + q` visible
queries. -/
theorem budgetHist_qBounded {Block : Type uBlock} {L : U128} {users : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (p q lambda : ℕ) :
    QBounded (budgetHist (users := users) model b S p q lambda) (p + q) := by
  intro l hbudget
  let queries : List.Vector (SequenceFunctionICQuery Block L users) l.length :=
    ⟨l, rfl⟩
  have hcount := primCount_add_evalCount queries
  simp only [budgetHist] at hbudget
  change primCount queries ≤ p ∧ evalCount queries ≤ q ∧ _ at hbudget
  omega

/-- The empty visible history satisfies every canonical SequenceFunction
budget. -/
theorem budgetHist_nil {Block : Type uBlock} {L : U128} {users : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (p q lambda : ℕ) :
    budgetHist (users := users) model b S p q lambda [] := by
  simp [budgetHist, primCount, evalCount]

/-- Appending a primitive query preserves the history budget whenever the
primitive counter still has room. -/
theorem budgetHist_append_prim
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    {l : List (SequenceFunctionICQuery Block L users)}
    (hbudget : budgetHist model b S p q lambda l)
    (hp : primCount
      (⟨l, rfl⟩ : List.Vector (SequenceFunctionICQuery Block L users) l.length) < p)
    (cb : HashOutput L × Block) :
    budgetHist model b S p q lambda (l ++ [.prim cb]) := by
  classical
  simp only [budgetHist] at hbudget ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [(taggedCounts_toList _).1] at hp
    simp only [List.Vector.toList_mk] at hp
    rw [(taggedCounts_toList _).1]
    simp only [List.Vector.toList_mk]
    simp
    omega
  · have hqOld := hbudget.2.1
    rw [(taggedCounts_toList _).2] at hqOld
    simp only [List.Vector.toList_mk] at hqOld
    rw [(taggedCounts_toList _).2]
    simp only [List.Vector.toList_mk]
    simpa using hqOld
  · intro e he
    exact hbudget.2.2 e (by simpa using he)

/-- Appending an evaluation query preserves the history budget whenever the
evaluation counter still has room and that request meets the cost cap. -/
theorem budgetHist_append_eval
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    {l : List (SequenceFunctionICQuery Block L users)}
    (hbudget : budgetHist model b S p q lambda l)
    (hq : evalCount
      (⟨l, rfl⟩ : List.Vector (SequenceFunctionICQuery Block L users) l.length) < q)
    (request : Fin users × InputSequence)
    (hcost : sequenceFunctionEvalCost model b S request ≤ lambda) :
    budgetHist model b S p q lambda (l ++ [.eval request]) := by
  classical
  simp only [budgetHist] at hbudget ⊢
  refine ⟨?_, ?_, ?_⟩
  · have hpOld := hbudget.1
    rw [(taggedCounts_toList _).1] at hpOld
    simp only [List.Vector.toList_mk] at hpOld
    rw [(taggedCounts_toList _).1]
    simp only [List.Vector.toList_mk]
    simpa using hpOld
  · rw [(taggedCounts_toList _).2] at hq
    simp only [List.Vector.toList_mk] at hq
    rw [(taggedCounts_toList _).2]
    simp only [List.Vector.toList_mk]
    simp
    omega
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact hbudget.2.2 e he
    · cases TaggedQuery.eval.inj he
      exact hcost

/-- The canonical SequenceFunction history budget can be completed one query
at a time.  The real trace bound supplies the evaluation-cost cap, output
backing supplies a primitive block, and `husers` supplies an evaluation user. -/
theorem budgetHist_qExtensible
    {Block : Type uBlock} {L : U128} {users p q lambda rK rS : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (htrace : SequenceFunctionTraceBound model b S lambda rK rS)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (husers : 0 < users) :
    QExtensible (budgetHist (users := users) model b S p q lambda) (p + q) := by
  classical
  letI : Nonempty Block := backed.nonemptyBlock
  intro l hbudget hlen
  let queries : List.Vector (SequenceFunctionICQuery Block L users) l.length :=
    ⟨l, rfl⟩
  have hsum : primCount queries + evalCount queries = l.length :=
    primCount_add_evalCount queries
  by_cases hp : primCount queries < p
  · exact ⟨.prim (model.iv, Classical.arbitrary Block),
      budgetHist_append_prim hbudget hp _⟩
  · have hq : evalCount queries < q := by
      have hp' := hbudget.1
      change primCount queries ≤ p at hp'
      have hq' := hbudget.2.1
      change evalCount queries ≤ q at hq'
      omega
    let request : Fin users × InputSequence :=
      (⟨0, husers⟩, Classical.arbitrary InputSequence)
    exact ⟨.eval request, budgetHist_append_eval hbudget hq request
      (htrace.evalCost_apply_le request)⟩

/--
At transcript length `p + q`, lifting the domain budget along the visible
input history is exactly the previously proved tagged transcript filter.
-/
theorem liftHist_budgetHist_eq {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) :
    liftHist (q := p + q) (budgetHist (users := users) model b S p q lambda) =
      SequenceFunctionTaggedBudgetRespects model b S p q lambda users := by
  funext t
  apply propext
  simp only [liftHist, budgetHist, SequenceFunctionTaggedBudgetRespects,
    TaggedBudgetRespects]
  rw [(taggedCounts_toList
    (⟨t.1.toList, rfl⟩ : List.Vector _ t.1.toList.length)).1,
    (taggedCounts_toList
      (⟨t.1.toList, rfl⟩ : List.Vector _ t.1.toList.length)).2,
    (taggedCounts_toList t.1).1,
    (taggedCounts_toList t.1).2]
  constructor
  · rintro ⟨hp, hq, hcost⟩
    refine ⟨hp, hq, ?_⟩
    intro i e hi
    apply hcost e
    rw [← hi]
    exact List.Vector.get_mem i t.1
  · rintro ⟨hp, hq, hcost⟩
    refine ⟨hp, hq, ?_⟩
    intro e he
    obtain ⟨i, hi⟩ := (List.Vector.mem_iff_get _ t.1).mp he
    exact hcost i e hi

/-! ## A4 Section 5 bound -/

/-- The cascade-inherent part of the SequenceMAC generic PRF bound. -/
def B_cascade (p q lambda c : ℕ) : NNReal :=
  (p * q * lambda : NNReal) / (2 : NNReal) ^ c +
    (Nat.choose q 2 : NNReal) *
      (((lambda + 2 : ℕ) : NNReal) / (2 : NNReal) ^ c +
        (64 * lambda ^ 4 : NNReal) / (2 : NNReal) ^ (2 * c))

/-- The raw-key repeat and secret-bearing input-guessing contribution. -/
def B_key (p users kappaStar : ℕ) : NNReal :=
  ((Nat.choose users 2 + 2 * users * p : ℕ) : NNReal) /
    (2 : NNReal) ^ kappaStar

/--
The additional cost of long key/customization derivations.  It vanishes when
`rK = rS = 0`.
-/
def deriveCostGeneric
    (p q users lambda rK rS c kappaStar : ℕ) : NNReal :=
  ((if 0 < rK then users * p else 0 : ℕ) : NNReal) /
      (2 : NNReal) ^ kappaStar +
    (rS * q * lambda : NNReal) / (2 : NNReal) ^ c +
    (((p + rS) * (users * rK) + Nat.choose (users * rK) 2 : ℕ) : NNReal) /
      (2 : NNReal) ^ c

/-- The SequenceMAC-specific R4 bound from A4 Section 5. -/
def B_SEQ (p q users lambda rK rS c kappaStar : ℕ) : NNReal :=
  B_cascade p q lambda c + B_key p users kappaStar +
    deriveCostGeneric p q users lambda rK rS c kappaStar

@[simp]
theorem deriveCostGeneric_zero (p q users lambda c kappaStar : ℕ) :
    deriveCostGeneric p q users lambda 0 0 c kappaStar = 0 := by
  simp [deriveCostGeneric]

/-! ## Filter-first R4 headline -/

/--
The structural tight generic-PRF theorem for canonical SequenceFunction.

The random-systems domain is budget-filtered first.  The normalization of
that filter and the ideal-extension bad-mass count remain the two separately
named R4-deep obligations; the proof itself is the bridge followed by the
already-proved equality-on-good endpoint.
-/
theorem sequenceMAC_generic_prf_tight
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (users p q lambda rK rS c kappaStar : ℕ)
    [Fintype Block] [DecidableEq Block]
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (huq : users ≤ q)
    (hkey : KeyPointMassBound keysP kappaStar)
    (htrace : SequenceFunctionTraceBound model b S lambda rK rS)
    (hroles : SequenceFunctionCrossRoleSeparated b S)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h_norm : DeltaFilterDomFiniteQueryNormalization
      (budgetHist (users := users) model b S p q lambda)
      (budgetHist_prefixClosed model b S p q lambda) (p + q)
      (sequenceFunctionICReal model b S users keysP).val
      (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).val)
    (h_badmass : ∀ E : QQueryEnvironment
        (SequenceFunctionICQuery Block L users) (SequenceFunctionICReply L)
        (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (extendedTranscriptDistRep (q := p + q)
        (sequenceFunctionICIdealP (Block := Block) (L := L) users keysP)
        sequenceFunctionICIdealF
        (sequenceFunctionICIdealReveal (p := p) (q := q) (lambda := lambda)
          model b S) E.1)
        (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
          B_SEQ p q users lambda rK rS c kappaStar) :
    (Δ(PFunPDS.filterDom
          (budgetHist (users := users) model b S p q lambda)
          (budgetHist_prefixClosed model b S p q lambda)
          (sequenceFunctionICReal model b S users keysP).val,
        PFunPDS.filterDom
          (budgetHist (users := users) model b S p q lambda)
          (budgetHist_prefixClosed model b S p q lambda)
          (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).val) : ℝ) ≤
      (B_SEQ p q users lambda rK rS c kappaStar : ℝ) := by
  calc
    (Δ(PFunPDS.filterDom
          (budgetHist (users := users) model b S p q lambda)
          (budgetHist_prefixClosed model b S p q lambda)
          (sequenceFunctionICReal model b S users keysP).val,
        PFunPDS.filterDom
          (budgetHist (users := users) model b S p q lambda)
          (budgetHist_prefixClosed model b S p q lambda)
          (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).val) : ℝ)
        ≤ filteredAdaptiveTranscriptAdvantage
            (liftHist (q := p + q)
              (budgetHist (users := users) model b S p q lambda))
            (sequenceFunctionICReal model b S users keysP)
            (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP) :=
      maxAdvantage_filterDom_le_filteredAdaptiveTranscriptAdvantage
        (q := p + q)
        (budgetHist (users := users) model b S p q lambda)
        (budgetHist_prefixClosed model b S p q lambda)
        (sequenceFunctionICReal model b S users keysP)
        (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP)
        (sequenceFunctionICReal_KStepTotal model b S users (p + q) keysP)
        (sequenceFunctionICIdeal_KStepTotal users (p + q) keysP)
        h_norm
    _ = filteredAdaptiveTranscriptAdvantage
          (SequenceFunctionTaggedBudgetRespects model b S p q lambda users)
          (sequenceFunctionICReal model b S users keysP)
          (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP) := by
      rw [liftHist_budgetHist_eq]
    _ ≤ (B_SEQ p q users lambda rK rS c kappaStar : ℝ) :=
      sequenceFunctionIC_r4_equality_on_good model b S backed keysP
        (B_SEQ p q users lambda rK rS c kappaStar) h_badmass

/-- The structural tight generic-PRF theorem with domain-filter
normalization discharged from the canonical SequenceFunction budget.  The
only remaining R4-deep premise is the ideal-extension bad-mass bound. -/
theorem sequenceMAC_generic_prf_tight_norm
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (users p q lambda rK rS c kappaStar : ℕ)
    [Fintype Block] [DecidableEq Block]
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (husers : 0 < users)
    (huq : users ≤ q)
    (hkey : KeyPointMassBound keysP kappaStar)
    (htrace : SequenceFunctionTraceBound model b S lambda rK rS)
    (hroles : SequenceFunctionCrossRoleSeparated b S)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h_badmass : ∀ E : QQueryEnvironment
        (SequenceFunctionICQuery Block L users) (SequenceFunctionICReply L)
        (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (extendedTranscriptDistRep (q := p + q)
        (sequenceFunctionICIdealP (Block := Block) (L := L) users keysP)
        sequenceFunctionICIdealF
        (sequenceFunctionICIdealReveal (p := p) (q := q) (lambda := lambda)
          model b S) E.1)
        (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
          B_SEQ p q users lambda rK rS c kappaStar) :
    (Δ(PFunPDS.filterDom
          (budgetHist (users := users) model b S p q lambda)
          (budgetHist_prefixClosed model b S p q lambda)
          (sequenceFunctionICReal model b S users keysP).val,
        PFunPDS.filterDom
          (budgetHist (users := users) model b S p q lambda)
          (budgetHist_prefixClosed model b S p q lambda)
          (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).val) : ℝ) ≤
      (B_SEQ p q users lambda rK rS c kappaStar : ℝ) := by
  apply sequenceMAC_generic_prf_tight model b S users p q lambda rK rS c kappaStar
    keysP huq hkey htrace hroles backed
  · exact deltaFilterDomFiniteQueryNormalization_of_extensible
      (budgetHist (users := users) model b S p q lambda)
      (budgetHist_prefixClosed model b S p q lambda) (p + q)
      (sequenceFunctionICReal model b S users keysP).val
      (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).val
      (budgetHist_qExtensible model b S htrace backed husers)
      (budgetHist_qBounded model b S p q lambda)
      (budgetHist_nil model b S p q lambda)
      (sequenceFunctionICReal_totalOnNonempty model b S users keysP)
      (sequenceFunctionICIdeal_totalOnNonempty users keysP)
  · exact h_badmass

end RandomSystemsModel
end SequenceHash
