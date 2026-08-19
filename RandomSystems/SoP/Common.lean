/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.FunctionEvaluator
import RandomSystems.QueryCompression
import RandomSystems.Coupling

/-!
# Shared infrastructure for SoP1 and SoP2

This file contains generic facts used by the permutation-sum proofs:

* transport from equality of CR18 system factors to equality of transcript
  laws;
* the half-`L¹` formula for statistical distance of finite probability laws;
* replay and saturation for systems obtained by sampling complete functions.

The last group is independent of any permutation-sum construction.  It says
that every adaptive transcript is deterministic postprocessing of the sampled
function table, and that a query schedule covering the finite input space
recovers the entire table.  Consequently the maximum adaptive advantage
saturates after `|X|` queries.

This module contains no SoP-specific model or quantitative estimate.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18

namespace RandomSystems.SoP.Common

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Equality of the system rectangles leaves the common environment
rectangle unchanged, hence gives equality of deterministic transcript laws. -/
theorem deterministic_transcript_dist_eq_of_system_factor_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    {q : Nat} (S T : PFunPDS.Prob X Y)
    (hfactor : ∀ (xv : List.Vector X q) (yv : List.Vector Y q),
      PFunPDE.transcriptSystemFactor S
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y) xv yv =
        PFunPDE.transcriptSystemFactor T
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y) xv yv)
    (E : PFunDDS.DDE X Y) :
    PFunPDS.Prob.deterministicTranscriptDist (q := q) S E =
      PFunPDS.Prob.deterministicTranscriptDist (q := q) T E := by
  ext t
  unfold PFunPDS.Prob.deterministicTranscriptDist
  rw [PFunPDE.deterministicTranscriptLawDist_apply,
    PFunPDE.deterministicTranscriptLawDist_apply]
  unfold PFunPDE.deterministicTranscriptLaw
  rw [PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    hfactor]

/-- Pointwise decomposition of an absolute difference into its two positive
parts. -/
private theorem abs_sub_eq_max_sub_add_max_sub (a b : ℝ) :
    |a - b| = max (a - b) 0 + max (b - a) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h),
      zero_add, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
      add_zero, abs_of_nonneg (sub_nonneg.mpr h)]

/-- For normalized finite laws, the repository's one-sided statistical
distance is the usual half-`L¹` distance. -/
theorem coe_statDist_eq_half_sum_abs
    {A : Type*} [Fintype A] (X Y : Dist.ProbDist A) :
    (RandomSystems.statDist X.val Y.val : ℝ) =
      (1 / 2 : ℝ) *
        ∑ a : A, |(X.val a : ℝ) - (Y.val a : ℝ)| := by
  have hsymm :
    RandomSystems.statDist X.val Y.val =
        RandomSystems.statDist Y.val X.val :=
    RandomSystems.statDist_symm_of_eq_weight X.val Y.val
      (X.property.weight_eq.trans Y.property.weight_eq.symm)
  have hsum :
      ∑ a : A, |(X.val a : ℝ) - (Y.val a : ℝ)| =
        (RandomSystems.statDist X.val Y.val : ℝ) +
          (RandomSystems.statDist Y.val X.val : ℝ) := by
    simp_rw [abs_sub_eq_max_sub_add_max_sub]
    rw [Finset.sum_add_distrib]
    rfl
  rw [hsum, ← hsymm]
  ring

/-!
## Sampled complete functions

The following infrastructure applies to any pair of systems obtained by first
sampling a complete function `X → Y` and then answering queries consistently
from that function.  The coin spaces and sampling maps may differ.

There are two structural directions.

1. For the upper bound, replay sends a complete table to the unique transcript
   it produces against a fixed deterministic environment.  We push a maximal
   coupling of the two table laws through this common replay map.  Equal tables
   remain equal transcripts, so the transcript disagreement probability cannot
   increase.
2. For the lower bound after `|X|` queries, a fixed schedule enumerates every
   input.  Its output vector determines the whole table, so data processing is
   lossless.

Combining the directions gives exact saturation, not merely monotonicity.
-/

section SampledFunctions

variable {X Y : Type*}
  [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Forget the original coins of a sampled-function experiment and retain
only its induced probability law on complete functions. -/
noncomputable def induced_function_law {Ω : Type*}
    (p : Dist.ProbDist Ω) (F : Ω → X → Y) :
    Dist.ProbDist (X → Y) :=
  ⟨Dist.fTransform F p.val,
    Dist.fTransform_isProbDist F p.property⟩

omit [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- Sampling coins and then embedding the sampled function as an evaluator is
the same law-level system as first passing to the induced complete-function
law. -/
theorem function_evaluator_eq_induced_function_law {Ω : Type*}
    (p : Dist.ProbDist Ω) (F : Ω → X → Y) :
    PFunPDS.Prob.functionEvaluator p F =
      PFunPDS.Prob.functionEvaluator
        (induced_function_law p F) (fun f : X → Y => f) := by
  apply Subtype.ext
  change
    Dist.fTransform (functionEvaluatorRV F) p.val =
      Dist.fTransform
        (functionEvaluatorRV (fun f : X → Y => f))
        (Dist.fTransform F p.val)
  rw [Dist.fTransform_comp]
  rfl

/-- Deterministically replay a complete function table against a total
`q`-query environment.  Totality gives existence and transcript uniqueness
makes the chosen prefix canonical up to equality. -/
noncomputable def function_law_replay {q : Nat}
    (E : PFunPDE.QQueryEnvironment X Y q) (f : X → Y) :
    PFunPDE.TranscriptPrefix X Y q :=
  Classical.choose
    (PFunPDE.transcriptJointEvent_exists_of_total
      (functionEvaluatorRV (fun f : X → Y => f))
      (fun _ : PUnit.{1} => E.1)
      (functionEvaluatorRV_KStepTotal
        (fun f : X → Y => f) q)
      (fun _ ys hlen => E.2 ys hlen)
      (f, PUnit.unit.{1}))

omit [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- The replayed prefix is the joint transcript generated by the supplied
function and deterministic environment. -/
theorem function_law_replay_spec {q : Nat}
    (E : PFunPDE.QQueryEnvironment X Y q) (f : X → Y) :
    PFunPDE.transcriptJointEvent
      (functionEvaluatorRV (fun f : X → Y => f))
      (fun _ : PUnit.{1} => E.1)
      (function_law_replay E f)
      (f, PUnit.unit.{1}) :=
  Classical.choose_spec
    (PFunPDE.transcriptJointEvent_exists_of_total
      (functionEvaluatorRV (fun f : X → Y => f))
      (fun _ : PUnit.{1} => E.1)
      (functionEvaluatorRV_KStepTotal
        (fun f : X → Y => f) q)
      (fun _ ys hlen => E.2 ys hlen)
      (f, PUnit.unit.{1}))

omit [DecidableEq X] [Nonempty X] [DecidableEq Y] [Nonempty Y] in
/-- The transcript law of a complete-function law is exactly its pushforward
through deterministic replay. -/
theorem deterministic_transcript_dist_function_law_eq_pushforward {q : Nat}
    (D : Dist.ProbDist (X → Y))
    (E : PFunPDE.QQueryEnvironment X Y q) :
    PFunPDS.Prob.deterministicTranscriptDist
        (q := q)
        (PFunPDS.Prob.functionEvaluator D (fun f : X → Y => f)) E.1 =
      Dist.fTransform (function_law_replay E) D.val := by
  ext t
  rw [Dist.fTransform_apply_eq_mass]
  unfold PFunPDS.Prob.deterministicTranscriptDist
  rw [PFunPDE.deterministicTranscriptLawDist_apply]
  unfold PFunPDS.Prob.functionEvaluator
  rw [PFunPDE.deterministicTranscriptLaw_pmf]
  rw [PFunPDE.transcriptLaw_apply,
    PFunPDE.transcriptDist_eq_mass_jointEvent]
  rw [Dist.prodProbDist_val, Dist.mass_prod_unitProbDist_right]
  congr 1
  funext f
  apply propext
  constructor
  · intro ht
    exact
      (PFunPDE.transcriptJointEvent_unique
        (functionEvaluatorRV (fun f : X → Y => f))
        (fun _ : PUnit.{1} => E.1)
        t (function_law_replay E f)
        (f, PUnit.unit.{1})
        ht (function_law_replay_spec E f)).symm
  · intro ht
    subst t
    exact function_law_replay_spec E f

omit [Nonempty X] [Nonempty Y] in
/-- Disagreement probability is the joint mass of the off-diagonal event. -/
private theorem coupling_disagreement_eq_mass
    {A : Type*} [Fintype A] [DecidableEq A]
    {D₀ D₁ : Dist A} (C : DistCoupling D₀ D₁) :
    C.prDisagree = C.joint.mass (fun p => p.1 ≠ p.2) := by
  rw [Dist.mass_eq_sum, DistCoupling.prDisagree, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.1 ≠ p.2 <;> simp [h]

omit [Nonempty X] [Nonempty Y] in
/-- Applying one deterministic map to both coordinates of a coupling cannot
increase its disagreement probability. -/
private theorem coupling_ftransform_disagreement_le
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    {D₀ D₁ : Dist A} (C : DistCoupling D₀ D₁) (f : A → B) :
    (C.fTransform f).prDisagree ≤ C.prDisagree := by
  rw [coupling_disagreement_eq_mass,
    coupling_disagreement_eq_mass]
  unfold DistCoupling.fTransform
  rw [Dist.mass_fTransform]
  apply Dist.mass_mono C.nonneg
  intro p hne
  exact fun hp => hne (congrArg f hp)

/-- A maximal coupling of two normalized complete-function laws. -/
private noncomputable def maximal_function_law_coupling
    (D₀ D₁ : Dist.ProbDist (X → Y)) :
    DistCoupling D₀.val D₁.val :=
  Classical.choose
    (RandomSystems.optimal_coupling_exists
      D₀.property.nonNeg D₁.property.nonNeg
      (D₀.property.weight_eq.trans D₁.property.weight_eq.symm))

omit [Nonempty X] [Nonempty Y] in
/-- The chosen complete-table coupling has disagreement probability equal to
the complete-table statistical distance. -/
private theorem maximal_function_law_coupling_disagreement
    (D₀ D₁ : Dist.ProbDist (X → Y)) :
    (maximal_function_law_coupling D₀ D₁).prDisagree =
      RandomSystems.statDist D₀.val D₁.val :=
  (Classical.choose_spec
    (RandomSystems.optimal_coupling_exists
      D₀.property.nonNeg D₁.property.nonNeg
      (D₀.property.weight_eq.trans D₁.property.weight_eq.symm))).symm

/-- Every adaptive transcript distance is bounded by the actual disagreement
probability of a maximal coupling of the two complete function tables. -/
private theorem adaptive_advantage_function_law_le_maximal_disagreement
    {q : Nat} (D₀ D₁ : Dist.ProbDist (X → Y)) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
        (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) ≤
      ((maximal_function_law_coupling D₀ D₁).prDisagree : ℝ) := by
  letI : Nonempty (PFunPDE.TranscriptPrefix X Y q) :=
    ⟨(List.Vector.ofFn (fun _ : Fin q => Classical.choice inferInstance),
      List.Vector.ofFn (fun _ : Fin q => Classical.choice inferInstance))⟩
  apply PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise_real
    _ _ (maximal_function_law_coupling D₀ D₁).prDisagree
    (maximal_function_law_coupling D₀ D₁).prDisagree_nonneg
  intro E
  rw [deterministic_transcript_dist_function_law_eq_pushforward D₀ E,
    deterministic_transcript_dist_function_law_eq_pushforward D₁ E]
  calc
    RandomSystems.statDist
        (Dist.fTransform (function_law_replay E) D₀.val)
        (Dist.fTransform (function_law_replay E) D₁.val) ≤
        ((maximal_function_law_coupling D₀ D₁).fTransform
          (function_law_replay E)).prDisagree :=
      RandomSystems.coupling_bound _
    _ ≤ (maximal_function_law_coupling D₀ D₁).prDisagree :=
      coupling_ftransform_disagreement_le
        (maximal_function_law_coupling D₀ D₁)
        (function_law_replay E)

/-- Every adaptive advantage between complete-function systems is at most the
statistical distance between their complete table laws. -/
theorem adaptive_advantage_function_law_le_stat_dist {q : Nat}
    (D₀ D₁ : Dist.ProbDist (X → Y)) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
        (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) ≤
      (RandomSystems.statDist D₀.val D₁.val : ℝ) := by
  rw [← maximal_function_law_coupling_disagreement D₀ D₁]
  exact adaptive_advantage_function_law_le_maximal_disagreement D₀ D₁

/-- A length-`q` fixed schedule covering every input once and then repeating
an arbitrary input. -/
private noncomputable def covering_queries (q : Nat) : Fin q → X :=
  fun i =>
    if h : i.1 < Fintype.card X then
      (Fintype.equivFin X).symm ⟨i.1, h⟩
    else Classical.choice (inferInstance : Nonempty X)

omit [DecidableEq X] in
/-- Once `q ≥ |X|`, the covering schedule visits every input. -/
private theorem covering_queries_surjective (q : Nat)
    (hq : Fintype.card X ≤ q) :
    Function.Surjective (covering_queries (X := X) q) := by
  intro x
  let j : Fin q :=
    ⟨Fintype.equivFin X x,
      lt_of_lt_of_le (Fintype.equivFin X x).isLt hq⟩
  refine ⟨j, ?_⟩
  simp [covering_queries, j]

omit [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- Evaluation on a covering schedule determines the complete function. -/
private theorem evaluate_covering_queries_injective (q : Nat)
    (hq : Fintype.card X ≤ q) :
    Function.Injective
      (fun f : X → Y =>
        fun i : Fin q => f (covering_queries (X := X) q i)) := by
  intro f g hfg
  funext x
  obtain ⟨i, hi⟩ := covering_queries_surjective (X := X) q hq x
  rw [← hi]
  exact congr_fun hfg i

omit [Nonempty Y] in
/-- Once the query budget covers the input space, one fixed schedule recovers
the complete-table statistical distance. -/
private theorem function_law_stat_dist_le_adaptive_advantage {q : Nat}
    (D₀ D₁ : Dist.ProbDist (X → Y))
    (hq : Fintype.card X ≤ q) :
    (RandomSystems.statDist D₀.val D₁.val : ℝ) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
        (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) := by
  let queries : Fin q → X := covering_queries (X := X) q
  let E : PFunPDE.QQueryEnvironment X Y q :=
    ⟨fixedQueryDDE (Y := Y) queries,
      fun ys hys =>
        fixedQueryEnvironment_KQueryTotal
          (Y := Y) queries PUnit.unit.{1} ys hys⟩
  have h :=
    PFunPDS.Prob.deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
      (q := q)
      (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
      (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f))
      E
  have h₀ :
      PFunPDS.Prob.deterministicTranscriptDist
          (q := q)
          (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
          E.1 =
        fixedInputLiftDist queries
          (Dist.fTransform
            (fun f : X → Y => fun i => f (queries i)) D₀.val) := by
    exact
      PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
        D₀ (fun f : X → Y => f) queries
  have h₁ :
      PFunPDS.Prob.deterministicTranscriptDist
          (q := q)
          (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f))
          E.1 =
        fixedInputLiftDist queries
          (Dist.fTransform
            (fun f : X → Y => fun i => f (queries i)) D₁.val) := by
    exact
      PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
        D₁ (fun f : X → Y => f) queries
  rw [h₀, h₁] at h
  have hout :
      (RandomSystems.statDist
        (Dist.fTransform
          (fun f : X → Y => fun i => f (queries i)) D₀.val)
        (Dist.fTransform
          (fun f : X → Y => fun i => f (queries i)) D₁.val) : ℝ) ≤
        PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q)
          (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
          (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) := by
    simpa only [fixedInputLiftDist,
      RandomSystems.statDist_fTransform_injective
        _ _ _ (fixedInputTranscriptPrefix_injective queries)] using h
  rw [RandomSystems.statDist_fTransform_injective _ _ _
    (by
      simpa [queries] using
        evaluate_covering_queries_injective (X := X) (Y := Y) q hq)] at hout
  exact hout

/-- After `|X|` queries, maximum adaptive advantage is exactly the statistical
distance between the two complete-function laws. -/
theorem adaptive_advantage_function_law_eq_stat_dist_of_card_le {q : Nat}
    (D₀ D₁ : Dist.ProbDist (X → Y))
    (hq : Fintype.card X ≤ q) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
        (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) =
      (RandomSystems.statDist D₀.val D₁.val : ℝ) :=
  le_antisymm
    (adaptive_advantage_function_law_le_stat_dist D₀ D₁)
    (function_law_stat_dist_le_adaptive_advantage D₀ D₁ hq)

/-- Every pair of complete-function systems saturates exactly at the cardinality
of the input space. -/
theorem adaptive_advantage_function_law_eq_min_card (q : Nat)
    (D₀ D₁ : Dist.ProbDist (X → Y)) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
        (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) =
      PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := min q (Fintype.card X))
        (PFunPDS.Prob.functionEvaluator D₀ (fun f : X → Y => f))
        (PFunPDS.Prob.functionEvaluator D₁ (fun f : X → Y => f)) := by
  rcases le_total q (Fintype.card X) with hq | hq
  · rw [Nat.min_eq_left hq]
  · rw [Nat.min_eq_right hq,
      adaptive_advantage_function_law_eq_stat_dist_of_card_le D₀ D₁ hq,
      adaptive_advantage_function_law_eq_stat_dist_of_card_le D₀ D₁ le_rfl]

/-- Direct sampled-function form: the original coin spaces and sampling maps
disappear before applying complete-table saturation. -/
theorem adaptive_advantage_sampled_functions_eq_min_card
    {Ω₀ Ω₁ : Type*}
    (p₀ : Dist.ProbDist Ω₀) (F₀ : Ω₀ → X → Y)
    (p₁ : Dist.ProbDist Ω₁) (F₁ : Ω₁ → X → Y)
    (q : Nat) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator p₀ F₀)
        (PFunPDS.Prob.functionEvaluator p₁ F₁) =
      PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := min q (Fintype.card X))
        (PFunPDS.Prob.functionEvaluator p₀ F₀)
        (PFunPDS.Prob.functionEvaluator p₁ F₁) := by
  rw [function_evaluator_eq_induced_function_law p₀ F₀,
    function_evaluator_eq_induced_function_law p₁ F₁]
  exact adaptive_advantage_function_law_eq_min_card q
    (induced_function_law p₀ F₀)
    (induced_function_law p₁ F₁)

/-- Lift an exact formula proved through `|X|` queries to every query budget by
evaluating it at `min(q, |X|)`. -/
theorem adaptive_advantage_sampled_functions_eq_bound_min_card
    {Ω₀ Ω₁ : Type*}
    (p₀ : Dist.ProbDist Ω₀) (F₀ : Ω₀ → X → Y)
    (p₁ : Dist.ProbDist Ω₁) (F₁ : Ω₁ → X → Y)
    (bound : Nat → ℝ)
    (hsmall : ∀ m, m ≤ Fintype.card X →
      PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := m)
          (PFunPDS.Prob.functionEvaluator p₀ F₀)
          (PFunPDS.Prob.functionEvaluator p₁ F₁) =
        bound m)
    (q : Nat) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q)
        (PFunPDS.Prob.functionEvaluator p₀ F₀)
        (PFunPDS.Prob.functionEvaluator p₁ F₁) =
      bound (min q (Fintype.card X)) := by
  rw [adaptive_advantage_sampled_functions_eq_min_card p₀ F₀ p₁ F₁ q]
  exact hsmall _ (Nat.min_le_right _ _)

end SampledFunctions

/-!
## Tape representatives and exact adaptive reduction

The complete-function saturation above is useful when the sampled object is an
entire function table.  The permutation-sum proofs use a different but closely
related representation: a length-`q` answer tape drives a deterministic lazy
system, and every adaptive interaction is deterministic replay of that tape.

The abstraction below isolates exactly that semantic pattern.  It deliberately
keeps the two directions of an exact reduction separate:

1. the adaptive upper bound pushes any tape coupling through common replay and
   is controlled by the coupling's actual disagreement event;
2. the lower bound uses one fixed-query experiment whose transcript exposes
   the entire tape.

Applications therefore retain explicit proof obligations for honest adaptive
marginals and for the fixed schedule that attains the tape distance.  No
permutation-sum object or quantitative estimate occurs in this section.
-/

/-- A deterministic CR18 representative driven by a finite answer tape.
The totality field is precisely what makes length-`q` replay exist. -/
structure TapeRepresentative
    (X Y : Type*) [Fintype X] [Fintype Y] (q : Nat) where
  to_dds : (Fin q → Y) → PFunDDS.DDS X Y
  k_step_total : PFunPDS.RV.KStepTotal to_dds q

namespace TapeRepresentative

variable {X Y : Type*}
  [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]
  {q : Nat}

/-- Sample a tape and expose its represented deterministic system. -/
noncomputable def prob
    (R : TapeRepresentative X Y q)
    (D : Dist.ProbDist (Fin q → Y)) : PFunPDS.Prob X Y :=
  Dist.PMF D R.to_dds

/-- Replay a deterministic adaptive environment against one fixed tape. -/
noncomputable def replay
    (R : TapeRepresentative X Y q)
    (E : PFunPDE.QQueryEnvironment X Y q)
    (tape : Fin q → Y) :
    PFunPDE.TranscriptPrefix X Y q :=
  Classical.choose
    (PFunPDE.transcriptJointEvent_exists_of_total
      R.to_dds
      (fun _ : PUnit.{1} => E.1)
      R.k_step_total
      (fun _ ys hlen => E.2 ys hlen)
      (tape, PUnit.unit.{1}))

omit [DecidableEq X] [DecidableEq Y] in
/-- The replayed prefix is the joint transcript generated by the supplied tape
and deterministic environment. -/
theorem replay_spec
    (R : TapeRepresentative X Y q)
    (E : PFunPDE.QQueryEnvironment X Y q)
    (tape : Fin q → Y) :
    PFunPDE.transcriptJointEvent
      R.to_dds
      (fun _ : PUnit.{1} => E.1)
      (R.replay E tape)
      (tape, PUnit.unit.{1}) :=
  Classical.choose_spec
    (PFunPDE.transcriptJointEvent_exists_of_total
      R.to_dds
      (fun _ : PUnit.{1} => E.1)
      R.k_step_total
      (fun _ ys hlen => E.2 ys hlen)
      (tape, PUnit.unit.{1}))

omit [DecidableEq X] [DecidableEq Y] in
/-- The transcript law of a sampled tape representative is deterministic
postprocessing of its tape law. -/
theorem deterministic_transcript_dist_prob_eq_f_transform
    (R : TapeRepresentative X Y q)
    (D : Dist.ProbDist (Fin q → Y))
    (E : PFunPDE.QQueryEnvironment X Y q) :
    PFunPDS.Prob.deterministicTranscriptDist
        (q := q) (R.prob D) E.1 =
      Dist.fTransform (R.replay E) D.val := by
  ext t
  rw [Dist.fTransform_apply_eq_mass]
  unfold PFunPDS.Prob.deterministicTranscriptDist
  rw [PFunPDE.deterministicTranscriptLawDist_apply]
  unfold prob
  rw [PFunPDE.deterministicTranscriptLaw_pmf]
  rw [PFunPDE.transcriptLaw_apply,
    PFunPDE.transcriptDist_eq_mass_jointEvent]
  rw [Dist.prodProbDist_val, Dist.mass_prod_unitProbDist_right]
  congr 1
  funext tape
  apply propext
  constructor
  · intro ht
    exact
      (PFunPDE.transcriptJointEvent_unique
        R.to_dds
        (fun _ : PUnit.{1} => E.1)
        t (R.replay E tape)
        (tape, PUnit.unit.{1})
        ht (R.replay_spec E tape)).symm
  · intro ht
    subst t
    exact R.replay_spec E tape

/-!
### Honest tape coupling

The maximal coupling is chosen once at tape level.  Its two named marginal
theorems are the normalization audit, while the disagreement theorem identifies
the exact probability later used by the adaptive upper bound.
-/

/-- A maximal coupling of two normalized tape laws. -/
noncomputable def maximal_coupling
    (D₀ D₁ : Dist.ProbDist (Fin q → Y)) :
    DistCoupling D₀.val D₁.val :=
  Classical.choose
    (optimal_coupling_exists D₀.property.nonNeg D₁.property.nonNeg
      (D₀.property.weight_eq.trans D₁.property.weight_eq.symm))

/-- The first marginal of the chosen maximal tape coupling. -/
theorem maximal_coupling_fst
    (D₀ D₁ : Dist.ProbDist (Fin q → Y)) :
    Dist.fTransform Prod.fst (maximal_coupling D₀ D₁).joint = D₀.val :=
  (maximal_coupling D₀ D₁).marginal_fst

/-- The second marginal of the chosen maximal tape coupling. -/
theorem maximal_coupling_snd
    (D₀ D₁ : Dist.ProbDist (Fin q → Y)) :
    Dist.fTransform Prod.snd (maximal_coupling D₀ D₁).joint = D₁.val :=
  (maximal_coupling D₀ D₁).marginal_snd

/-- The chosen maximal coupling disagrees with probability exactly equal to
the statistical distance between its tape marginals. -/
theorem maximal_coupling_disagreement
    (D₀ D₁ : Dist.ProbDist (Fin q → Y)) :
    (maximal_coupling D₀ D₁).prDisagree =
      statDist D₀.val D₁.val :=
  (Classical.choose_spec
    (optimal_coupling_exists D₀.property.nonNeg D₁.property.nonNeg
      (D₀.property.weight_eq.trans D₁.property.weight_eq.symm))).symm

/-!
### Adaptive upper bound

First replace the concrete systems by their honest tape representatives.
Their transcript laws are then common deterministic replay of the two tape
laws.  Data processing and the coupling lemma bound every environment by the
actual tape-disagreement event.
-/

/-- For one adaptive environment, honest tape marginals and common replay
bound transcript distance by the disagreement probability of any tape
coupling. -/
theorem deterministic_transcript_distance_le_coupling
    (R : TapeRepresentative X Y q)
    (real ideal : PFunPDS.Prob X Y)
    (D₀ D₁ : Dist.ProbDist (Fin q → Y))
    (C : DistCoupling D₀.val D₁.val)
    (E : PFunPDE.QQueryEnvironment X Y q)
    (hreal :
      PFunPDS.Prob.deterministicTranscriptDist (q := q) real E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₀) E.1)
    (hideal :
      PFunPDS.Prob.deterministicTranscriptDist (q := q) ideal E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₁) E.1) :
    statDist
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) real E.1)
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) ideal E.1) ≤
      C.prDisagree := by
  -- Both concrete transcript laws are honest replay marginals.
  rw [hreal, hideal,
    R.deterministic_transcript_dist_prob_eq_f_transform,
    R.deterministic_transcript_dist_prob_eq_f_transform]
  -- Common replay is data processing; the coupling lemma then measures the
  -- remaining tape distance by the coupling's real failure event.
  exact
    (statDist_fTransform_le D₀.val D₁.val (R.replay E)).trans
      (coupling_bound C)

/-- If both concrete systems have the honest tape marginals against every
deterministic adaptive environment, their adaptive advantage is bounded by
the actual disagreement probability of any coupling of those tapes. -/
theorem adaptive_advantage_le_coupling
    (R : TapeRepresentative X Y q)
    (real ideal : PFunPDS.Prob X Y)
    (D₀ D₁ : Dist.ProbDist (Fin q → Y))
    (C : DistCoupling D₀.val D₁.val)
    (hreal : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      PFunPDS.Prob.deterministicTranscriptDist (q := q) real E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₀) E.1)
    (hideal : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      PFunPDS.Prob.deterministicTranscriptDist (q := q) ideal E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₁) E.1) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) real ideal ≤
      (C.prDisagree : ℝ) := by
  apply PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise_real
    real ideal C.prDisagree C.prDisagree_nonneg
  intro E
  exact R.deterministic_transcript_distance_le_coupling
    real ideal D₀ D₁ C E (hreal E) (hideal E)

/-- Maximal-coupling specialization of the adaptive tape upper bound. -/
theorem adaptive_advantage_le_tape_distance
    (R : TapeRepresentative X Y q)
    (real ideal : PFunPDS.Prob X Y)
    (D₀ D₁ : Dist.ProbDist (Fin q → Y))
    (hreal : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      PFunPDS.Prob.deterministicTranscriptDist (q := q) real E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₀) E.1)
    (hideal : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      PFunPDS.Prob.deterministicTranscriptDist (q := q) ideal E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₁) E.1) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) real ideal ≤
      (statDist D₀.val D₁.val : ℝ) := by
  rw [← maximal_coupling_disagreement D₀ D₁]
  exact R.adaptive_advantage_le_coupling
    real ideal D₀ D₁ (maximal_coupling D₀ D₁) hreal hideal

/-!
### Fixed-query lower bound and exactness

The lower bound is intentionally independent of the representative `R`.
An application supplies one schedule whose real and ideal fixed-query laws are
the injective transcript lifts of the two tape laws.  This exposes the complete
tape distance inside the adaptive supremum.
-/

/-- A fixed-query experiment exposing both complete tapes witnesses their
statistical distance inside adaptive distinguishing advantage. -/
theorem tape_distance_le_adaptive_advantage_fixed_query
    (real ideal : PFunPDS.Prob X Y)
    (D₀ D₁ : Dist.ProbDist (Fin q → Y))
    (xs : Fin q → X)
    (hreal :
      PFunPDS.Prob.fixedQueryTranscriptDist real xs =
        fixedInputLiftDist xs D₀.val)
    (hideal :
      PFunPDS.Prob.fixedQueryTranscriptDist ideal xs =
        fixedInputLiftDist xs D₁.val) :
    (statDist D₀.val D₁.val : ℝ) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) real ideal := by
  -- The scheduled fixed-query environment is a legitimate point in the
  -- adaptive supremum, including the zero-query boundary case.
  let E : PFunPDE.QQueryEnvironment X Y q :=
    ⟨fixedQueryDDE (Y := Y) xs,
      fun ys hys =>
        fixedQueryEnvironment_KQueryTotal
          (Y := Y) xs PUnit.unit.{1} ys hys⟩
  have h :=
    PFunPDS.Prob.deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
      (q := q) real ideal E
  change
    (statDist
      (PFunPDS.Prob.fixedQueryTranscriptDist real xs)
      (PFunPDS.Prob.fixedQueryTranscriptDist ideal xs) : ℝ) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) real ideal at h
  rw [hreal, hideal] at h
  -- The fixed-input transcript embedding is injective, so it preserves the
  -- tape statistical distance exactly.
  simpa only [fixedInputLiftDist,
    statDist_fTransform_injective
      _ _ _ (fixedInputTranscriptPrefix_injective xs)] using h

/-- Exact reduction from adaptive distinguishing to tape statistical distance,
assembled only after the adaptive coupling upper bound and fixed-query lower
bound have both been proved. -/
theorem adaptive_advantage_eq_tape_distance
    (R : TapeRepresentative X Y q)
    (real ideal : PFunPDS.Prob X Y)
    (D₀ D₁ : Dist.ProbDist (Fin q → Y))
    (xs : Fin q → X)
    (hreal_adaptive : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      PFunPDS.Prob.deterministicTranscriptDist (q := q) real E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₀) E.1)
    (hideal_adaptive : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      PFunPDS.Prob.deterministicTranscriptDist (q := q) ideal E.1 =
        PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (R.prob D₁) E.1)
    (hreal_fixed :
      PFunPDS.Prob.fixedQueryTranscriptDist real xs =
        fixedInputLiftDist xs D₀.val)
    (hideal_fixed :
      PFunPDS.Prob.fixedQueryTranscriptDist ideal xs =
        fixedInputLiftDist xs D₁.val) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) real ideal =
      (statDist D₀.val D₁.val : ℝ) :=
  le_antisymm
    (R.adaptive_advantage_le_tape_distance
      real ideal D₀ D₁ hreal_adaptive hideal_adaptive)
    (tape_distance_le_adaptive_advantage_fixed_query
      real ideal D₀ D₁ xs hreal_fixed hideal_fixed)

end TapeRepresentative

end RandomSystems.SoP.Common
