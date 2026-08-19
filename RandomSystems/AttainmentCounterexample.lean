/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem
import RandomSystems.CondEquiv

/-!
# A varying-domain counterexample to unrestricted attainment

This module is a project/model regression, not a theorem of
Lanzenberger--Maurer.  It refutes the attempted extension of their
common-domain attainment theorem to all partial CR18 systems.

The source semantics used here were checked directly in the original CR18
PDF: Definition 3.2 and Definition 3.3 on printed pages 57--58 (PDF leaf 35),
and Definitions 3.6--3.7 on printed pages 59--60 (PDF leaf 36).  A rejected
query produces the visible answer `bot`, is deleted only from the history seen
by the underlying DDS, and does not stop the environment.

There are two Boolean queries and one ordinary answer.  The four deterministic
atoms answer at the root on neither query, only `false`, only `true`, or both;
after one accepted query they all self-destruct.  The normalized laws are

```
S = 1/2 * both + 1/2 * neither,
T = 1/2 * false-only + 1/2 * true-only.
```

Their optimal transcript advantage is `1/2`.  Nevertheless transcript
equivalence fixes the entire four-valued root-answer-pattern law, whose two
displayed distributions are disjoint.  Therefore every equivalent
representative pair has static distance one and the unrestricted class
distance is one.
-/

namespace RandomSystems.CR18.AttainmentCounterexample

open RandomSystems (Dist)

/-! ## The four self-destructing deterministic atoms -/

/-- The inert deterministic system, which answers no query. -/
def rootNeitherSystem : PFunDDS.DDS Bool PUnit :=
  PFunDDS.DDS.empty

/-- The deterministic system that answers only the root query `false`. -/
def rootFalseSystem : PFunDDS.DDS Bool PUnit :=
  PFunDDS.DDS.prepend false (some PUnit.unit) rootNeitherSystem

/-- The deterministic system that answers only the root query `true`. -/
def rootTrueSystem : PFunDDS.DDS Bool PUnit :=
  PFunDDS.DDS.prepend true (some PUnit.unit) rootNeitherSystem

/-- The deterministic system that answers either root query and then
self-destructs. -/
def rootBothSystem : PFunDDS.DDS Bool PUnit :=
  PFunDDS.DDS.glue fun query =>
    PFunDDS.DDS.prepend query (some PUnit.unit) rootNeitherSystem

/-- The half-mass used by both normalized laws. -/
noncomputable def halfMass : ℝ := 1 / 2

theorem halfMass_nonneg : (0 : ℝ) ≤ halfMass := by norm_num [halfMass]

/-- A point mass at a non-negative weight is a non-negative law. -/
private theorem single_nonNeg {A : Type*} (a : A) {c : ℝ} (hc : 0 ≤ c) :
    Dist.NonNeg (Finsupp.single a c : Dist A) := fun b => by
  classical
  rw [Finsupp.single_apply]
  split
  · exact hc
  · exact le_rfl

/-- `S = 1/2 * both + 1/2 * neither`. -/
noncomputable def fourPatternSource : PFunPDS Bool PUnit :=
  Finsupp.single rootBothSystem halfMass +
    Finsupp.single rootNeitherSystem halfMass

/-- `T = 1/2 * false-only + 1/2 * true-only`. -/
noncomputable def fourPatternTarget : PFunPDS Bool PUnit :=
  Finsupp.single rootFalseSystem halfMass +
    Finsupp.single rootTrueSystem halfMass

private theorem weight_add {A : Type*} (mu nu : Dist A) :
    (mu + nu).weight = mu.weight + nu.weight := by
  rw [Dist.weight_eq_finsupp_sum, Dist.weight_eq_finsupp_sum,
    Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

private theorem weight_single {A : Type*} (a : A) (c : ℝ) :
    Dist.weight (Finsupp.single a c : Dist A) = c := by
  rw [Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_single_index rfl

theorem four_pattern_source_has_weight_one :
    fourPatternSource.weight = 1 := by
  rw [fourPatternSource, weight_add, weight_single, weight_single]
  norm_num [halfMass]

theorem four_pattern_target_has_weight_one :
    fourPatternTarget.weight = 1 := by
  rw [fourPatternTarget, weight_add, weight_single, weight_single]
  norm_num [halfMass]

/-- Both displayed laws are non-negative — structural on the `NNReal` carrier,
a two-line check on the signed one. -/
theorem four_pattern_source_nonNeg : fourPatternSource.NonNeg := fun s =>
  add_nonneg (single_nonNeg _ halfMass_nonneg s)
    (single_nonNeg _ halfMass_nonneg s)

theorem four_pattern_target_nonNeg : fourPatternTarget.NonNeg := fun s =>
  add_nonneg (single_nonNeg _ halfMass_nonneg s)
    (single_nonNeg _ halfMass_nonneg s)

/-- The source law packaged at the normalized public boundary. -/
noncomputable def fourPatternSourceProb : PFunPDS.Prob Bool PUnit :=
  ⟨fourPatternSource, four_pattern_source_nonNeg,
    four_pattern_source_has_weight_one⟩

/-- The target law packaged at the normalized public boundary. -/
noncomputable def fourPatternTargetProb : PFunPDS.Prob Bool PUnit :=
  ⟨fourPatternTarget, four_pattern_target_nonNeg,
    four_pattern_target_has_weight_one⟩

/-! ## The root-answer-pattern observable -/

/-- The observable answer to one query at the root of a deterministic system. -/
noncomputable def rootAnswer (system : PFunDDS.DDS Bool PUnit)
    (query : Bool) : Option PUnit :=
  PFunDDS.output (PFunDDS.fullyDefined system) [query]
    (by rw [PFunDDS.dom_fullyDefined]; simp)

/-- The four-valued law-level statistic recording whether each Boolean query
is answered at the root. -/
noncomputable def rootAnswerPattern
    (system : PFunDDS.DDS Bool PUnit) : Option PUnit × Option PUnit :=
  (rootAnswer system false, rootAnswer system true)

/-- Push a PDS forward to its law of root-answer patterns. -/
noncomputable def rootAnswerPatternLaw (system : PFunPDS Bool PUnit) :
    Dist (Option PUnit × Option PUnit) :=
  Dist.fTransform rootAnswerPattern system

private theorem ftransform_add {A B : Type*} (f : A → B)
    (mu nu : Dist A) :
    Dist.fTransform f (mu + nu) =
      Dist.fTransform f mu + Dist.fTransform f nu := by
  exact Finsupp.mapDomain_add

private theorem ftransform_single {A B : Type*} (f : A → B)
    (a : A) (c : ℝ) :
    Dist.fTransform f (Finsupp.single a c) =
      Finsupp.single (f a) c := by
  show Finsupp.mapDomain f _ = _
  exact Finsupp.mapDomain_single

private theorem root_both_answers_every_query (query : Bool) :
    rootAnswer rootBothSystem query = some PUnit.unit := by
  unfold rootAnswer rootBothSystem
  exact output_fullyDefined_glue_prepend
    (fun _ => some PUnit.unit) (fun _ => rootNeitherSystem) query

private theorem root_false_answers_false :
    rootAnswer rootFalseSystem false = some PUnit.unit := by
  unfold rootAnswer rootFalseSystem
  exact output_fullyDefined_prepend false (some PUnit.unit) rootNeitherSystem

private theorem root_false_rejects_true :
    rootAnswer rootFalseSystem true = none := by
  apply output_fullyDefined_eq_none_iff.mpr
  rw [rootFalseSystem, dom_prepend_some]
  simp

private theorem root_true_rejects_false :
    rootAnswer rootTrueSystem false = none := by
  apply output_fullyDefined_eq_none_iff.mpr
  rw [rootTrueSystem, dom_prepend_some]
  simp

private theorem root_true_answers_true :
    rootAnswer rootTrueSystem true = some PUnit.unit := by
  unfold rootAnswer rootTrueSystem
  exact output_fullyDefined_prepend true (some PUnit.unit) rootNeitherSystem

private theorem root_neither_rejects_every_query (query : Bool) :
    rootAnswer rootNeitherSystem query = none := by
  apply output_fullyDefined_eq_none_iff.mpr
  exact not_mem_dom_empty [query]

private theorem root_answer_pattern_both :
    rootAnswerPattern rootBothSystem =
      (some PUnit.unit, some PUnit.unit) := by
  simp [rootAnswerPattern, root_both_answers_every_query]

private theorem root_answer_pattern_false :
    rootAnswerPattern rootFalseSystem = (some PUnit.unit, none) := by
  simp [rootAnswerPattern, root_false_answers_false, root_false_rejects_true]

private theorem root_answer_pattern_true :
    rootAnswerPattern rootTrueSystem = (none, some PUnit.unit) := by
  simp [rootAnswerPattern, root_true_rejects_false, root_true_answers_true]

private theorem root_answer_pattern_neither :
    rootAnswerPattern rootNeitherSystem = (none, none) := by
  simp [rootAnswerPattern, root_neither_rejects_every_query]

theorem four_pattern_source_root_answer_pattern_law :
    rootAnswerPatternLaw fourPatternSource =
      Finsupp.single (some PUnit.unit, some PUnit.unit) halfMass +
        Finsupp.single (none, none) halfMass := by
  unfold rootAnswerPatternLaw fourPatternSource
  rw [ftransform_add, ftransform_single, ftransform_single,
    root_answer_pattern_both,
    root_answer_pattern_neither]

theorem four_pattern_target_root_answer_pattern_law :
    rootAnswerPatternLaw fourPatternTarget =
      Finsupp.single (some PUnit.unit, none) halfMass +
        Finsupp.single (none, some PUnit.unit) halfMass := by
  unfold rootAnswerPatternLaw fourPatternTarget
  rw [ftransform_add, ftransform_single, ftransform_single,
    root_answer_pattern_false,
    root_answer_pattern_true]

/-! ## Failure of the source common-domain hypothesis -/

private theorem root_both_ne_root_neither :
    rootBothSystem ≠ rootNeitherSystem := by
  intro h
  have hp := congrArg rootAnswerPattern h
  rw [root_answer_pattern_both, root_answer_pattern_neither] at hp
  exact Option.some_ne_none PUnit.unit (Prod.mk.inj hp).1

private theorem root_both_mem_source_support :
    rootBothSystem ∈ fourPatternSource.support := by
  rw [Finsupp.mem_support_iff]
  simp [fourPatternSource, root_both_ne_root_neither, halfMass]

private theorem root_neither_mem_source_support :
    rootNeitherSystem ∈ fourPatternSource.support := by
  rw [Finsupp.mem_support_iff]
  simp [fourPatternSource, root_both_ne_root_neither, halfMass]

private theorem root_both_accepts_false :
    [false] ∈ PFunDDS.dom rootBothSystem := by
  unfold rootBothSystem
  exact (cons_mem_dom_glue _ false []).mpr
    (singleton_mem_dom_prepend_some false PUnit.unit rootNeitherSystem)

/-- The displayed normalized pair is outside Lanzenberger--Maurer's source
theorem boundary: there is no one domain shared by every support atom on both
sides (indeed, the source law alone already has varying domains). -/
theorem four_pattern_pair_has_no_common_support_domain :
    ¬ ∃ domain : Set (List Bool),
      (∀ system ∈ fourPatternSource.support,
        PFunDDS.dom system = domain) ∧
      (∀ system ∈ fourPatternTarget.support,
        PFunDDS.dom system = domain) := by
  rintro ⟨domain, hsource, _htarget⟩
  have hboth := hsource rootBothSystem root_both_mem_source_support
  have hneither := hsource rootNeitherSystem root_neither_mem_source_support
  have hdomains : PFunDDS.dom rootBothSystem =
      PFunDDS.dom rootNeitherSystem := hboth.trans hneither.symm
  exact not_mem_dom_empty [false]
    (hdomains ▸ root_both_accepts_false)

/-! ## Transcript extraction of the root pattern -/

/-- Ask `first`; after an observed rejection ask `second`; otherwise stop. -/
def queryThenOtherAfterRejection (first second : Bool) :
    PFunDDS.DDE Bool PUnit
  | [] => some first
  | [none] => some second
  | _ => none

/-- CR18's skip semantics makes the two-query experiment read the second root
answer after the first query is rejected. -/
private theorem transcript_query_then_other_after_rejection_eq
    (system : PFunDDS.DDS Bool PUnit) (first second : Bool) :
    PFunDDS.transcript system
        (queryThenOtherAfterRejection first second) 2 =
      match rootAnswer system first with
      | none =>
          [(first, none), (second, rootAnswer system second)]
      | some _ => [(first, some PUnit.unit)] := by
  rw [show 2 = 1 + 1 by omega,
    transcript_successor system
      (queryThenOtherAfterRejection first second) (by rfl) 1]
  change (first, rootAnswer system first) ::
      PFunDDS.transcript (PFunDDS.DDS.successor system first)
        (PFunDDS.DDE.successor
          (queryThenOtherAfterRejection first second)
          (rootAnswer system first)) 1 = _
  cases hfirst : rootAnswer system first with
  | none =>
      have hnot : [first] ∉ PFunDDS.dom system :=
        output_fullyDefined_eq_none_iff.mp hfirst
      rw [successor_of_not_mem hnot]
      rw [transcript_successor system
        (PFunDDS.DDE.successor
          (queryThenOtherAfterRejection first second) none)
        (x := second) (by rfl) 0]
      rfl
  | some answer =>
      cases answer
      rfl

/-- The two-entry transcript occurs exactly when the first query is rejected
and the second has the specified root answer. -/
private theorem transcript_query_then_other_after_rejection_eq_two_entries_iff
    (system : PFunDDS.DDS Bool PUnit) (first second : Bool)
    (answer : Option PUnit) :
    PFunDDS.transcript system
        (queryThenOtherAfterRejection first second) 2 =
        [(first, none), (second, answer)] ↔
      rootAnswer system first = none ∧
        rootAnswer system second = answer := by
  rw [transcript_query_then_other_after_rejection_eq]
  cases hfirst : rootAnswer system first with
  | none => simp
  | some value => cases value; simp

private theorem ordered_root_answer_pair_mass_eq_two_query_transcript_value
    (system : PFunPDS Bool PUnit) (first second : Bool)
    (answer : Option PUnit) :
    (Dist.fTransform
        (fun deterministic =>
          (rootAnswer deterministic first, rootAnswer deterministic second))
        system) (none, answer) =
      transcriptDist system
        (queryThenOtherAfterRejection first second) 2
        [(first, none), (second, answer)] := by
  rw [Dist.fTransform_apply_eq_mass, transcriptDist,
    Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr system
  intro deterministic
  simpa only [Prod.mk.injEq] using
    (transcript_query_then_other_after_rejection_eq_two_entries_iff
      deterministic first second answer).symm

private theorem root_answer_pattern_law_none_none_eq_transcript_value
    (system : PFunPDS Bool PUnit) :
    rootAnswerPatternLaw system (none, none) =
      transcriptDist system
        (queryThenOtherAfterRejection false true) 2
        [(false, none), (true, none)] := by
  unfold rootAnswerPatternLaw rootAnswerPattern
  exact ordered_root_answer_pair_mass_eq_two_query_transcript_value
    system false true none

private theorem root_answer_pattern_law_none_some_eq_transcript_value
    (system : PFunPDS Bool PUnit) :
    rootAnswerPatternLaw system (none, some PUnit.unit) =
      transcriptDist system
        (queryThenOtherAfterRejection false true) 2
        [(false, none), (true, some PUnit.unit)] := by
  unfold rootAnswerPatternLaw rootAnswerPattern
  exact ordered_root_answer_pair_mass_eq_two_query_transcript_value
    system false true (some PUnit.unit)

private theorem root_answer_pattern_law_some_none_eq_transcript_value
    (system : PFunPDS Bool PUnit) :
    rootAnswerPatternLaw system (some PUnit.unit, none) =
      transcriptDist system
        (queryThenOtherAfterRejection true false) 2
        [(true, none), (false, some PUnit.unit)] := by
  rw [rootAnswerPatternLaw, Dist.fTransform_apply_eq_mass, transcriptDist,
    Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr system
  intro deterministic
  have hread :=
    (transcript_query_then_other_after_rejection_eq_two_entries_iff
      deterministic true false (some PUnit.unit)).symm
  simpa only [rootAnswerPattern, Prod.mk.injEq, and_comm] using hread

private theorem root_answer_pattern_law_weight_eq_sum_four_values
    (law : Dist (Option PUnit × Option PUnit)) :
    law.weight =
      law (none, none) + law (none, some PUnit.unit) +
        law (some PUnit.unit, none) +
          law (some PUnit.unit, some PUnit.unit) := by
  rw [Dist.weight_eq_finsupp_sum,
    Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  simp
  ac_rfl

/-- Transcript equivalence preserves the complete four-valued distribution of
root acceptance patterns.  The three cells containing a rejection are read by
the concrete two-query CR18 experiments above; the fourth follows from the
preserved total weight. -/
theorem equivalent_laws_have_equal_root_answer_pattern_laws
    {left right : PFunPDS Bool PUnit} (h : Equivalent left right) :
    rootAnswerPatternLaw left = rootAnswerPatternLaw right := by
  classical
  have hnone_none :
      rootAnswerPatternLaw left (none, none) =
        rootAnswerPatternLaw right (none, none) := by
    rw [root_answer_pattern_law_none_none_eq_transcript_value,
      root_answer_pattern_law_none_none_eq_transcript_value,
      h (queryThenOtherAfterRejection false true) 2]
  have hnone_some :
      rootAnswerPatternLaw left (none, some PUnit.unit) =
        rootAnswerPatternLaw right (none, some PUnit.unit) := by
    rw [root_answer_pattern_law_none_some_eq_transcript_value,
      root_answer_pattern_law_none_some_eq_transcript_value,
      h (queryThenOtherAfterRejection false true) 2]
  have hsome_none :
      rootAnswerPatternLaw left (some PUnit.unit, none) =
        rootAnswerPatternLaw right (some PUnit.unit, none) := by
    rw [root_answer_pattern_law_some_none_eq_transcript_value,
      root_answer_pattern_law_some_none_eq_transcript_value,
      h (queryThenOtherAfterRejection true false) 2]
  have hweight :
      (rootAnswerPatternLaw left).weight =
        (rootAnswerPatternLaw right).weight := by
    unfold rootAnswerPatternLaw
    rw [Dist.weight_fTransform, Dist.weight_fTransform,
      weight_eq_of_equivalent h]
  have hsome_some :
      rootAnswerPatternLaw left (some PUnit.unit, some PUnit.unit) =
        rootAnswerPatternLaw right (some PUnit.unit, some PUnit.unit) := by
    rw [root_answer_pattern_law_weight_eq_sum_four_values,
      root_answer_pattern_law_weight_eq_sum_four_values,
      hnone_none, hnone_some, hsome_none] at hweight
    exact add_left_cancel hweight
  apply Finsupp.ext
  rintro ⟨leftAnswer, rightAnswer⟩
  cases leftAnswer with
  | none =>
      cases rightAnswer with
      | none => exact hnone_none
      | some value => cases value; exact hnone_some
  | some value =>
      cases value
      cases rightAnswer with
      | none => exact hsome_none
      | some value => cases value; exact hsome_some

/-! ## The optimal transcript advantage is one half -/

private theorem root_both_successor_eq_neither (query : Bool) :
    PFunDDS.DDS.successor rootBothSystem query = rootNeitherSystem := by
  unfold rootBothSystem
  exact successor_glue_prepend
    (fun _ => some PUnit.unit) (fun _ => rootNeitherSystem) query rfl

private theorem root_false_successor_eq_neither :
    PFunDDS.DDS.successor rootFalseSystem false = rootNeitherSystem := by
  unfold rootFalseSystem
  exact successor_prepend false PUnit.unit rootNeitherSystem

private theorem root_true_successor_eq_neither :
    PFunDDS.DDS.successor rootTrueSystem true = rootNeitherSystem := by
  unfold rootTrueSystem
  exact successor_prepend true PUnit.unit rootNeitherSystem

private theorem root_both_and_root_false_have_equal_transcripts_after_false
    (environment : PFunDDS.DDE Bool PUnit) (fuel : Nat)
    (hfirst : environment [] = some false) :
    PFunDDS.transcript rootBothSystem environment fuel =
      PFunDDS.transcript rootFalseSystem environment fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [transcript_successor rootBothSystem environment hfirst fuel,
        transcript_successor rootFalseSystem environment hfirst fuel]
      change (false, rootAnswer rootBothSystem false) ::
          PFunDDS.transcript (PFunDDS.DDS.successor rootBothSystem false)
            (PFunDDS.DDE.successor environment
              (rootAnswer rootBothSystem false)) fuel =
        (false, rootAnswer rootFalseSystem false) ::
          PFunDDS.transcript (PFunDDS.DDS.successor rootFalseSystem false)
            (PFunDDS.DDE.successor environment
              (rootAnswer rootFalseSystem false)) fuel
      rw [root_both_answers_every_query, root_false_answers_false,
        root_both_successor_eq_neither, root_false_successor_eq_neither]

private theorem root_both_and_root_true_have_equal_transcripts_after_true
    (environment : PFunDDS.DDE Bool PUnit) (fuel : Nat)
    (hfirst : environment [] = some true) :
    PFunDDS.transcript rootBothSystem environment fuel =
      PFunDDS.transcript rootTrueSystem environment fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [transcript_successor rootBothSystem environment hfirst fuel,
        transcript_successor rootTrueSystem environment hfirst fuel]
      change (true, rootAnswer rootBothSystem true) ::
          PFunDDS.transcript (PFunDDS.DDS.successor rootBothSystem true)
            (PFunDDS.DDE.successor environment
              (rootAnswer rootBothSystem true)) fuel =
        (true, rootAnswer rootTrueSystem true) ::
          PFunDDS.transcript (PFunDDS.DDS.successor rootTrueSystem true)
            (PFunDDS.DDE.successor environment
              (rootAnswer rootTrueSystem true)) fuel
      rw [root_both_answers_every_query, root_true_answers_true,
        root_both_successor_eq_neither, root_true_successor_eq_neither]

private theorem transcript_eq_nil_of_environment_stops_initially
    {environment : PFunDDS.DDE Bool PUnit} (hstop : environment [] = none)
    (system : PFunDDS.DDS Bool PUnit) :
    ∀ fuel, PFunDDS.transcript system environment fuel = [] := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [transcript_succ_stall (by rw [ih]; exact hstop), ih]

private theorem source_transcript_distribution_eq_two_atoms
    (environment : PFunDDS.DDE Bool PUnit) (fuel : Nat) :
    transcriptDist fourPatternSource environment fuel =
      Finsupp.single
          (PFunDDS.transcript rootBothSystem environment fuel) halfMass +
        Finsupp.single
          (PFunDDS.transcript rootNeitherSystem environment fuel) halfMass := by
  unfold transcriptDist fourPatternSource
  rw [ftransform_add, ftransform_single, ftransform_single]

private theorem target_transcript_distribution_eq_two_atoms
    (environment : PFunDDS.DDE Bool PUnit) (fuel : Nat) :
    transcriptDist fourPatternTarget environment fuel =
      Finsupp.single
          (PFunDDS.transcript rootFalseSystem environment fuel) halfMass +
        Finsupp.single
          (PFunDDS.transcript rootTrueSystem environment fuel) halfMass := by
  unfold transcriptDist fourPatternTarget
  rw [ftransform_add, ftransform_single, ftransform_single]

/-- The `δ`-over-a-superset form, at the signed carrier's spelling
(`max (μ a − ν a) 0`), with the second law non-negative so the padding cells
contribute nothing.  Delegates to the library lemma. -/
private theorem delta_eq_sum_of_support_subset {A : Type*} {mu nu : Dist A}
    (hnu : nu.NonNeg) {support : Finset A} (hsub : mu.support ⊆ support) :
    δ mu nu = ∑ a ∈ support, max (mu a - nu a) 0 :=
  δ_eq_sum_of_support_subset hnu hsub

private theorem delta_add_same_left {A : Type*}
    {common left right : Dist A} (hcommon : common.NonNeg)
    (hright : right.NonNeg) :
    δ (common + left) (common + right) = δ left right := by
  classical
  rw [delta_eq_sum_of_support_subset (fun a => add_nonneg (hcommon a) (hright a))
      (Finset.subset_union_left :
        (common + left).support ⊆
          (common + left).support ∪ left.support),
    delta_eq_sum_of_support_subset hright
      (Finset.subset_union_right :
        left.support ⊆ (common + left).support ∪ left.support)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.add_apply, Finsupp.add_apply]
  ring_nf

private theorem delta_two_half_mixtures_with_one_common_atom_le_half
    {A : Type*} (common left right : A) :
    δ (Finsupp.single common halfMass + Finsupp.single left halfMass)
        (Finsupp.single common halfMass + Finsupp.single right halfMass)
      ≤ halfMass := by
  rw [delta_add_same_left (single_nonNeg common halfMass_nonneg)
    (single_nonNeg right halfMass_nonneg)]
  exact (δ_le_weight (single_nonNeg left halfMass_nonneg)
    (single_nonNeg right halfMass_nonneg)).trans_eq (weight_single left halfMass)

private theorem four_pattern_transcript_distance_le_half
    (environment : PFunDDS.DDE Bool PUnit) (fuel : Nat) :
    δ (transcriptDist fourPatternSource environment fuel)
        (transcriptDist fourPatternTarget environment fuel) ≤ halfMass := by
  rw [source_transcript_distribution_eq_two_atoms,
    target_transcript_distribution_eq_two_atoms]
  cases hfirst : environment [] with
  | none =>
      rw [transcript_eq_nil_of_environment_stops_initially hfirst,
        transcript_eq_nil_of_environment_stops_initially hfirst,
        transcript_eq_nil_of_environment_stops_initially hfirst,
        transcript_eq_nil_of_environment_stops_initially hfirst,
        δ_self]
      exact halfMass_nonneg
  | some query =>
      cases query with
      | false =>
          rw [root_both_and_root_false_have_equal_transcripts_after_false
            environment fuel hfirst]
          exact delta_two_half_mixtures_with_one_common_atom_le_half _ _ _
      | true =>
          rw [root_both_and_root_true_have_equal_transcripts_after_true
            environment fuel hfirst]
          rw [add_comm
            (Finsupp.single
              (PFunDDS.transcript rootFalseSystem environment fuel) halfMass)
            (Finsupp.single
              (PFunDDS.transcript rootTrueSystem environment fuel) halfMass)]
          exact delta_two_half_mixtures_with_one_common_atom_le_half _ _ _

private theorem root_both_false_then_true_transcript :
    PFunDDS.transcript rootBothSystem
        (queryThenOtherAfterRejection false true) 2 =
      [(false, some PUnit.unit)] := by
  rw [transcript_query_then_other_after_rejection_eq,
    root_both_answers_every_query]

private theorem root_neither_false_then_true_transcript :
    PFunDDS.transcript rootNeitherSystem
        (queryThenOtherAfterRejection false true) 2 =
      [(false, none), (true, none)] := by
  rw [transcript_query_then_other_after_rejection_eq,
    root_neither_rejects_every_query,
    root_neither_rejects_every_query]

private theorem root_false_false_then_true_transcript :
    PFunDDS.transcript rootFalseSystem
        (queryThenOtherAfterRejection false true) 2 =
      [(false, some PUnit.unit)] := by
  rw [transcript_query_then_other_after_rejection_eq,
    root_false_answers_false]

private theorem root_true_false_then_true_transcript :
    PFunDDS.transcript rootTrueSystem
        (queryThenOtherAfterRejection false true) 2 =
      [(false, none), (true, some PUnit.unit)] := by
  rw [transcript_query_then_other_after_rejection_eq,
    root_true_rejects_false, root_true_answers_true]

private theorem displayed_two_query_transcript_distance_eq_half :
    δ (transcriptDist fourPatternSource
          (queryThenOtherAfterRejection false true) 2)
        (transcriptDist fourPatternTarget
          (queryThenOtherAfterRejection false true) 2) = halfMass := by
  rw [source_transcript_distribution_eq_two_atoms,
    target_transcript_distribution_eq_two_atoms,
    root_both_false_then_true_transcript,
    root_neither_false_then_true_transcript,
    root_false_false_then_true_transcript,
    root_true_false_then_true_transcript,
    delta_add_same_left (single_nonNeg _ halfMass_nonneg)
      (single_nonNeg _ halfMass_nonneg)]
  unfold δ
  rw [Finsupp.sum_single_index (by simp)]
  simp [halfMass]

/-- The unrestricted CR18 transcript advantage of the normalized four-pattern
pair is exactly one half. -/
theorem four_pattern_optimal_advantage_eq_one_half :
    Adv fourPatternSource fourPatternTarget = (1 / 2 : Real) := by
  unfold Adv
  apply le_antisymm
  · refine csSup_le
      ⟨_, queryThenOtherAfterRejection false true, 2, rfl⟩ ?_
    rintro value ⟨environment, fuel, rfl⟩
    have hbound := four_pattern_transcript_distance_le_half environment fuel
    simpa [halfMass] using hbound
  · calc
      (1 / 2 : Real) =
          δ (transcriptDist fourPatternSource
              (queryThenOtherAfterRejection false true) 2)
            (transcriptDist fourPatternTarget
              (queryThenOtherAfterRejection false true) 2) := by
            rw [displayed_two_query_transcript_distance_eq_half]
            norm_num [halfMass]
      _ ≤ sSup {value : Real | ∃ (environment : PFunDDS.DDE Bool PUnit)
          (fuel : Nat),
          value =
            (δ (transcriptDist fourPatternSource environment fuel)
              (transcriptDist fourPatternTarget environment fuel) : Real)} :=
        le_csSup
          (bddAbove_adv_set four_pattern_source_nonNeg four_pattern_target_nonNeg)
          ⟨queryThenOtherAfterRejection false true, 2, rfl⟩

/-! ## Every equivalent representative pair has static distance one -/

theorem four_pattern_root_answer_pattern_distance_eq_one :
    δ (rootAnswerPatternLaw fourPatternSource)
        (rootAnswerPatternLaw fourPatternTarget) = 1 := by
  rw [four_pattern_source_root_answer_pattern_law,
    four_pattern_target_root_answer_pattern_law]
  rw [delta_eq_sum_of_support_subset
    (nu := Finsupp.single (some PUnit.unit, none) halfMass +
      Finsupp.single (none, some PUnit.unit) halfMass)
    (fun a => add_nonneg (single_nonNeg _ halfMass_nonneg a)
      (single_nonNeg _ halfMass_nonneg a))
    (support :=
      {(some PUnit.unit, some PUnit.unit), (none, none)})]
  · simp [halfMass]
    norm_num
  · intro pattern hpattern
    by_contra houtside
    have hneBoth :
        pattern ≠ (some PUnit.unit, some PUnit.unit) := by
      simpa using fun h => houtside (Finset.mem_insert.mpr (Or.inl h))
    have hneNeither : pattern ≠ (none, none) := by
      simpa using fun h => houtside
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    rw [Finsupp.mem_support_iff] at hpattern
    exact hpattern (by simp [hneBoth, hneNeither])

/-- Data processing under the root-pattern statistic forces every pair of
transcript-equivalent representatives to retain all one unit of static
distance. -/
theorem four_pattern_equivalent_representatives_have_static_distance_at_least_one
    {left right : PFunPDS Bool PUnit} (hrightnn : right.NonNeg)
    (hleft : Equivalent left fourPatternSource)
    (hright : Equivalent right fourPatternTarget) :
    (1 : ℝ) ≤ δ left right := by
  have hleftPattern :=
    equivalent_laws_have_equal_root_answer_pattern_laws hleft
  have hrightPattern :=
    equivalent_laws_have_equal_root_answer_pattern_laws hright
  have hdata := δ_fTransform_le rootAnswerPattern left hrightnn
  change δ (rootAnswerPatternLaw left) (rootAnswerPatternLaw right) ≤
    δ left right at hdata
  rw [hleftPattern, hrightPattern,
    four_pattern_root_answer_pattern_distance_eq_one] at hdata
  exact hdata

/-- Normalization supplies the matching upper bound, so every representative
pair in the two transcript-equivalence classes has static distance exactly
one. -/
theorem four_pattern_equivalent_representatives_have_static_distance_one
    {left right : PFunPDS Bool PUnit} (hleftnn : left.NonNeg)
    (hrightnn : right.NonNeg)
    (hleft : Equivalent left fourPatternSource)
    (hright : Equivalent right fourPatternTarget) :
    δ left right = 1 := by
  apply le_antisymm
  · refine (δ_le_weight hleftnn hrightnn).trans_eq ?_
    rw [weight_eq_of_equivalent hleft,
      four_pattern_source_has_weight_one]
  · exact
      four_pattern_equivalent_representatives_have_static_distance_at_least_one
        hrightnn hleft hright

/-- The entire source equivalence class is at static distance one from the
entire target equivalence class. -/
theorem four_pattern_class_distance_eq_one :
    Δ fourPatternSource fourPatternTarget = 1 := by
  unfold Δ
  have hvalues :
      {a : ℝ | ∃ left right : PFunPDS Bool PUnit,
        left.NonNeg ∧ right.NonNeg ∧
        Equivalent left fourPatternSource ∧
          Equivalent right fourPatternTarget ∧
          a = (δ left right : ℝ)} = {(1 : ℝ)} := by
    ext a
    constructor
    · rintro ⟨left, right, hleftnn, hrightnn, hleft, hright, rfl⟩
      rw [Set.mem_singleton_iff]
      exact
        four_pattern_equivalent_representatives_have_static_distance_one
          hleftnn hrightnn hleft hright
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      refine ⟨fourPatternSource, fourPatternTarget,
        four_pattern_source_nonNeg, four_pattern_target_nonNeg,
        (fun _ _ => rfl), (fun _ _ => rfl), ?_⟩
      symm
      exact
        four_pattern_equivalent_representatives_have_static_distance_one
          four_pattern_source_nonNeg four_pattern_target_nonNeg
          (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hvalues, csInf_singleton]

/-- The unrestricted varying-domain model refutes the representative-distance
characterization of optimal distinguishing advantage: the class distance is
one, while the optimal advantage is one half. -/
theorem four_pattern_unrestricted_class_distance_ne_optimal_advantage :
    Δ fourPatternSource fourPatternTarget ≠
      Adv fourPatternSource fourPatternTarget := by
  rw [four_pattern_class_distance_eq_one,
    four_pattern_optimal_advantage_eq_one_half]
  norm_num

/-! ## CR18 Definition 3.19 does not refine thesis Def 2.17 on partial systems

CR18 Definition 3.18's behavior kernel `b(S)` conditions on **successful**
histories only: a rejected query never enters the conditioning event, so the
kernel cannot see the correlations a rejection reveals.  The four
self-destructing atoms above turn the docstring sketch of `RandomSystem.lean`
(§ "CR18 cumulative observable behavior") into a kernel-checked theorem: the
two displayed probability laws have identical Definition 3.18 kernels at every
index and argument (`four_pattern_behavior_eq`), yet the two-query
skip-semantics environment already used for the attainment counterexample
separates their transcript laws (`four_pattern_not_equivalent`).  Hence CR18
Definition 3.19 equivalence (`≡ᵦ`) is **strictly coarser** than the thesis's
resource-level Definition 2.17 equivalence (`Equivalent`) on partial systems;
the behavior notion that does match transcript laws is Definition 3.20's
cumulative `Option`-behavior of `s⊥`
(`behavior_equivalent_iff_transcript_equivalent`). -/

/- `Dist`-level plumbing, private copies pending upstreaming into `Dist.lean`
(same convention as `weight_add`/`ftransform_add` above). -/

private theorem mass_add {A : Type*} (mu nu : Dist A) (P : A → Prop) :
    (mu + nu).mass P = mu.mass P + nu.mass P := by
  unfold Dist.mass
  exact Finsupp.sum_add_index' (fun a => by simp)
    (fun a w₁ w₂ => by by_cases h : P a <;> simp [h])

open Classical in
private theorem mass_single {A : Type*} (a : A) (c : ℝ) (P : A → Prop) :
    Dist.mass (Finsupp.single a c) P = if P a then c else 0 := by
  unfold Dist.mass
  rw [Finsupp.sum_single_index (by by_cases h : P a <;> simp [h])]

/-- `Dist.cond` reads only the conditioning mass and the conjunction mass, so
two conditionals agree — including their partiality domains — whenever those
two masses agree. -/
private theorem cond_congr_of_mass_eq {A : Type*} {S T : Dist A}
    {P Q P' Q' : A → Prop}
    (hQ : S.mass Q = T.mass Q')
    (hPQ : S.mass (fun a => P a ∧ Q a) = T.mass (fun a => P' a ∧ Q' a)) :
    S.cond P Q = T.cond P' Q' := by
  unfold Dist.cond
  rw [hPQ, hQ]

/-- The joint atom answers exactly the two singleton histories. -/
private theorem mem_dom_rootBothSystem_iff (l : List Bool) :
    l ∈ PFunDDS.dom rootBothSystem ↔ l = [false] ∨ l = [true] := by
  cases l with
  | nil =>
      exact iff_of_false (PFunDDS.empty_not_mem _)
        (by rintro (h | h) <;> cases h)
  | cons x m =>
      unfold rootBothSystem
      rw [cons_mem_dom_glue, dom_prepend_some]
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨m', hm', -⟩)
        · cases x
          · exact Or.inl h
          · exact Or.inr h
        · exact absurd hm' (not_mem_dom_empty m')
      · rintro (h | h) <;> exact Or.inl (by injection h with h1 h2; rw [h1, h2])

/-- The `false`-only atom answers exactly `[false]`. -/
private theorem mem_dom_rootFalseSystem_iff (l : List Bool) :
    l ∈ PFunDDS.dom rootFalseSystem ↔ l = [false] := by
  unfold rootFalseSystem
  rw [dom_prepend_some]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨m', hm', -⟩)
    · exact h
    · exact absurd hm' (not_mem_dom_empty m')
  · exact Or.inl

/-- The `true`-only atom answers exactly `[true]`. -/
private theorem mem_dom_rootTrueSystem_iff (l : List Bool) :
    l ∈ PFunDDS.dom rootTrueSystem ↔ l = [true] := by
  unfold rootTrueSystem
  rw [dom_prepend_some]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨m', hm', -⟩)
    · exact h
    · exact absurd hm' (not_mem_dom_empty m')
  · exact Or.inl

/-- Every accepted history of one of the four atoms has length one: the atoms
self-destruct after their first answer.  This is the load-bearing fact that
blinds the successful-history kernel — no successful history of length `≥ 1`
has any continuation, so the kernel never conditions past round one. -/
private theorem length_eq_one_of_mem_dom_atom {s : PFunDDS.DDS Bool PUnit}
    (hs : s = rootBothSystem ∨ s = rootNeitherSystem ∨ s = rootFalseSystem ∨
      s = rootTrueSystem)
    {l : List Bool} (hl : l ∈ PFunDDS.dom s) : l.length = 1 := by
  rcases hs with rfl | rfl | rfl | rfl
  · rcases (mem_dom_rootBothSystem_iff l).mp hl with rfl | rfl <;> rfl
  · exact absurd hl (not_mem_dom_empty l)
  · rw [(mem_dom_rootFalseSystem_iff l).mp hl]; rfl
  · rw [(mem_dom_rootTrueSystem_iff l).mp hl]; rfl

open Classical in
private theorem mass_fourPatternSource (P : PFunDDS.DDS Bool PUnit → Prop) :
    fourPatternSource.mass P =
      (if P rootBothSystem then halfMass else 0) +
        (if P rootNeitherSystem then halfMass else 0) := by
  unfold fourPatternSource
  rw [mass_add, mass_single, mass_single]

open Classical in
private theorem mass_fourPatternTarget (P : PFunDDS.DDS Bool PUnit → Prop) :
    fourPatternTarget.mass P =
      (if P rootFalseSystem then halfMass else 0) +
        (if P rootTrueSystem then halfMass else 0) := by
  unfold fourPatternTarget
  rw [mass_add, mass_single, mass_single]

/-- Either single-query domain event has source mass one half (`both` accepts,
`neither` rejects). -/
private theorem mass_source_singleton_dom (x : Bool) :
    fourPatternSource.mass (fun s => [x] ∈ PFunDDS.dom s) = halfMass := by
  rw [mass_fourPatternSource,
    if_pos ((mem_dom_rootBothSystem_iff [x]).mpr (by cases x <;> simp)),
    if_neg (show [x] ∉ PFunDDS.dom rootNeitherSystem from
      not_mem_dom_empty [x]),
    add_zero]

/-- Either single-query domain event has target mass one half (exactly one of
the two one-sided atoms accepts). -/
private theorem mass_target_singleton_dom (x : Bool) :
    fourPatternTarget.mass (fun s => [x] ∈ PFunDDS.dom s) = halfMass := by
  cases x
  · rw [mass_fourPatternTarget,
      if_pos ((mem_dom_rootFalseSystem_iff [false]).mpr rfl),
      if_neg (fun h => by
        simpa using (mem_dom_rootTrueSystem_iff [false]).mp h),
      add_zero]
  · rw [mass_fourPatternTarget,
      if_neg (fun h => by
        simpa using (mem_dom_rootFalseSystem_iff [true]).mp h),
      if_pos ((mem_dom_rootTrueSystem_iff [true]).mpr rfl), zero_add]

/-- **CR18 Definition 3.19 equivalence holds**: the two four-pattern laws have
the same Definition 3.18 successful-history kernel at every round and every
argument.  Round one sees mass one half on either query on both sides; the
conditioning event of round two is the answered first query (mass one half on
both sides) while the conditioned event is an accepted length-two history
(mass zero — every atom self-destructs); from round three on the conditioning
event itself already requires an accepted length-two history, so both kernels
are undefined.  The rejection correlations that distinguish the two laws never
enter any of these events. -/
theorem four_pattern_behavior_eq :
    PFunPDS.BehaviorEq fourPatternSource fourPatternTarget := by
  funext i arg
  obtain ⟨y, xs, ys⟩ := arg
  -- `simp only` unfolds the kernel and discharges the `PUnit` output
  -- equations (`Subsingleton`), leaving pure domain-membership events.
  simp only [PFunPDS.behavior]
  have hatoms_source : ∀ P : PFunDDS.DDS Bool PUnit → Prop,
      (¬ P rootBothSystem) → (¬ P rootNeitherSystem) →
      Dist.mass fourPatternSource P = 0 := fun P h1 h2 => by
    rw [mass_fourPatternSource, if_neg h1, if_neg h2, add_zero]
  have hatoms_target : ∀ P : PFunDDS.DDS Bool PUnit → Prop,
      (¬ P rootFalseSystem) → (¬ P rootTrueSystem) →
      Dist.mass fourPatternTarget P = 0 := fun P h1 h2 => by
    rw [mass_fourPatternTarget, if_neg h1, if_neg h2, add_zero]
  match i with
  | 0 =>
      have hys : ys.toList.length = 0 := by simp
      obtain ⟨x, hx⟩ : ∃ x, xs.toList = [x] :=
        List.length_eq_one_iff.mp (by simp)
      have htriv : ∀ s : PFunDDS.DDS Bool PUnit,
          (∀ k : Fin ys.toList.length,
            ∃ _ : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s, True) ↔ True :=
        fun s => iff_of_true (fun k => Fin.elim0 (hys ▸ k)) trivial
      refine cond_congr_of_mass_eq ?_ ?_
      · rw [Dist.mass_congr fourPatternSource htriv,
          Dist.mass_congr fourPatternTarget htriv,
          Dist.mass_true, Dist.mass_true,
          four_pattern_source_has_weight_one,
          four_pattern_target_has_weight_one]
      · have hconj : ∀ s : PFunDDS.DDS Bool PUnit,
            ((∃ _ : xs.toList ∈ PFunDDS.dom s, True) ∧
              (∀ k : Fin ys.toList.length,
                ∃ _ : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s, True)) ↔
              xs.toList ∈ PFunDDS.dom s :=
          fun s => ⟨fun ⟨⟨hd, _⟩, _⟩ => hd,
            fun hd => ⟨⟨hd, trivial⟩, fun k => Fin.elim0 (hys ▸ k)⟩⟩
        rw [Dist.mass_congr fourPatternSource hconj,
          Dist.mass_congr fourPatternTarget hconj]
        simp only [hx]
        rw [mass_source_singleton_dom, mass_target_singleton_dom]
  | 1 =>
      have hys : ys.toList.length = 1 := by simp
      obtain ⟨x₁, x₂, hx⟩ : ∃ a b, xs.toList = [a, b] :=
        List.length_eq_two.mp (by simp)
      have htake : xs.toList.take 1 = [x₁] := by rw [hx]; rfl
      have hQ : ∀ s : PFunDDS.DDS Bool PUnit,
          (∀ k : Fin ys.toList.length,
            ∃ _ : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s, True) ↔
            [x₁] ∈ PFunDDS.dom s := by
        intro s
        constructor
        · intro h
          obtain ⟨hd, -⟩ := h ⟨0, by omega⟩
          simpa [htake] using hd
        · intro hmem k
          have hk : k.1 = 0 := by have := k.2; omega
          refine ⟨?_, trivial⟩
          rw [hk, zero_add, htake]
          exact hmem
      refine cond_congr_of_mass_eq ?_ ?_
      · rw [Dist.mass_congr fourPatternSource hQ,
          Dist.mass_congr fourPatternTarget hQ,
          mass_source_singleton_dom, mass_target_singleton_dom]
      · have hfalse : ∀ s : PFunDDS.DDS Bool PUnit,
            (s = rootBothSystem ∨ s = rootNeitherSystem ∨
              s = rootFalseSystem ∨ s = rootTrueSystem) →
            ¬ ((∃ _ : xs.toList ∈ PFunDDS.dom s, True) ∧
              (∀ k : Fin ys.toList.length,
                ∃ _ : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s, True)) := by
          rintro s hs ⟨⟨hd, -⟩, -⟩
          have hlen := length_eq_one_of_mem_dom_atom hs hd
          rw [hx] at hlen
          simp at hlen
        rw [hatoms_source _ (hfalse _ (Or.inl rfl))
            (hfalse _ (Or.inr (Or.inl rfl))),
          hatoms_target _ (hfalse _ (Or.inr (Or.inr (Or.inl rfl))))
            (hfalse _ (Or.inr (Or.inr (Or.inr rfl))))]
  | (n + 2) =>
      have hys : ys.toList.length = n + 2 := by simp
      have hxs : xs.toList.length = n + 3 := by simp
      have hQfalse : ∀ s : PFunDDS.DDS Bool PUnit,
          (s = rootBothSystem ∨ s = rootNeitherSystem ∨
            s = rootFalseSystem ∨ s = rootTrueSystem) →
          ¬ (∀ k : Fin ys.toList.length,
              ∃ _ : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s, True) := by
        intro s hs h
        obtain ⟨hd, -⟩ := h ⟨1, by omega⟩
        have hd' : xs.toList.take 2 ∈ PFunDDS.dom s := by simpa using hd
        have hlen := length_eq_one_of_mem_dom_atom hs hd'
        rw [List.length_take, hxs] at hlen
        omega
      refine cond_congr_of_mass_eq ?_ ?_
      · rw [hatoms_source _ (hQfalse _ (Or.inl rfl))
            (hQfalse _ (Or.inr (Or.inl rfl))),
          hatoms_target _ (hQfalse _ (Or.inr (Or.inr (Or.inl rfl))))
            (hQfalse _ (Or.inr (Or.inr (Or.inr rfl))))]
      · rw [hatoms_source _ (fun h => hQfalse _ (Or.inl rfl) h.2)
            (fun h => hQfalse _ (Or.inr (Or.inl rfl)) h.2),
          hatoms_target _
            (fun h => hQfalse _ (Or.inr (Or.inr (Or.inl rfl))) h.2)
            (fun h => hQfalse _ (Or.inr (Or.inr (Or.inr rfl))) h.2)]

/-- **Thesis Def 2.17 equivalence fails**: the two-query experiment that
requeries after a rejection reads the rejection correlations and separates
the transcript laws at distance one half. -/
theorem four_pattern_not_equivalent :
    ¬ Equivalent fourPatternSource fourPatternTarget := by
  intro h
  have hδ := displayed_two_query_transcript_distance_eq_half
  rw [h (queryThenOtherAfterRejection false true) 2, δ_self] at hδ
  exact absurd hδ.symm (by simp [halfMass])

/-- **CR18 Definition 3.18's kernel provably loses correlations on partial
systems** (the headline): two probability laws over deterministic systems with
equal Definition 3.18 behavior kernels whose transcript laws differ.  At the
resource level the thesis's transcript notion (Def 2.17), not CR18's
successful-history kernel (Def 3.18/3.19), is the right equivalence for
partial systems.  The matching positive result — on *total* systems the Def 3.18
kernel equality **does** coincide with `Equivalent` — is
`behaviorEq_iff_equivalent_of_total` below; note that this is a statement about
Def 3.18's `PFunPDS.behavior`, *not* about
`behavior_equivalent_iff_transcript_equivalent`, which compares Def 3.20's
cumulative `s⊥`-behavior and is a different object. -/
theorem behaviorEq_not_equivalent_counterexample :
    ∃ S T : PFunPDS Bool PUnit,
      S.weight = 1 ∧ T.weight = 1 ∧
        PFunPDS.BehaviorEq S T ∧ ¬ Equivalent S T :=
  ⟨fourPatternSource, fourPatternTarget,
    four_pattern_source_has_weight_one, four_pattern_target_has_weight_one,
    four_pattern_behavior_eq, four_pattern_not_equivalent⟩

/-! ## The positive half: on total systems Def 3.18 *is* thesis Def 2.17

The counterexample above shows that CR18 Definition 3.18's successful-history
kernel is strictly coarser than transcript equivalence **on partial systems**.
The reason is domain information: the four atoms differ only in *which* queries
they reject, and the kernel conditions rejections away.  Where domains carry no
information the objection disappears, and the two notions coincide.

"Where domains carry no information" is `CondEquiv.TotalOnNonempty`: every
deterministic system in the law's support accepts every nonempty history.  That
is the honest hypothesis rather than `PFunPDS.HasFixedDomain S {l | l ≠ []}`:
the two are equivalent (`totalOnNonempty_iff_hasFixedDomain`, proved below —
`[] ∉ dom s` is forced by `PFunDDS.Valid`, so the fixed-domain form adds
nothing), and `TotalOnNonempty` is the form the rest of the tree already uses
for "Maurer's systems, defined on the histories under discussion".  It is also
the weaker-looking of the two, so stating the theorem with it is the stronger
reading.

The proof factors through the **successful-history mass** `successMass`, the
one event both sides are assembled from:

* Def 3.18's kernel is literally `Dist.cond` of two such masses
  (`behavior_apply`), so equal masses give equal kernels and — via the
  conditional chain rule, here run as an induction on the answer list rather
  than through `cumulativeBehavior_eq_behavior_prod`'s `Vector` product — equal
  kernels give equal masses (`successMass_eq_of_behaviorEq`);
* on total systems Def 3.20's `observableBehavior` on `s⊥` *is* `successMass`
  at the all-answered transcripts and vanishes at every transcript containing a
  `⊥` (`observableBehavior_zip_eq_successMass`,
  `observableBehavior_eq_zero_of_getElem_none`), which is exactly where
  totality enters and exactly what the counterexample violates.

Composing with `behavior_equivalent_iff_transcript_equivalent` (Def 3.20 ↔
Def 2.17) closes the loop. -/

section TotalSystems

open RandomSystems.CR18.CondEquiv (TotalOnNonempty)

universe u v

variable {X : Type u} {Y : Type v}

/-! ### `Dist`-level plumbing for the conditional chain rule -/

/-- Support-restricted congruence for event masses: only atoms the law actually
charges matter.  `Dist.mass_congr` asks for the equivalence everywhere, which
a support-level hypothesis such as `TotalOnNonempty` cannot supply. -/
private theorem mass_congr_of_support {A : Type*} (S : Dist A) {P Q : A → Prop}
    (h : ∀ a ∈ S.support, (P a ↔ Q a)) : S.mass P = S.mass Q := by
  classical
  unfold Dist.mass
  refine Finsupp.sum_congr fun a ha => ?_
  by_cases hP : P a
  · rw [if_pos hP, if_pos ((h a ha).mp hP)]
  · rw [if_neg hP, if_neg fun hq => hP ((h a ha).mpr hq)]

/-- The converse of `cond_congr_of_mass_eq`: equal conditionals together with
equal normalizers force equal joint masses.  This is the single step of the
CR18 eq. (3.2) chain rule, run at the mass level. -/
private theorem mass_and_eq_of_cond_eq {A : Type*} {S T : Dist A}
    (hS0 : S.NonNeg) (hT0 : T.NonNeg) {P Q P' Q' : A → Prop}
    (hQ : S.mass Q = T.mass Q')
    (hcond : S.cond P Q = T.cond P' Q') :
    S.mass (fun a => P a ∧ Q a) = T.mass (fun a => P' a ∧ Q' a) := by
  by_cases hzero : S.mass Q = 0
  · have hzero' : T.mass Q' = 0 := hQ ▸ hzero
    have hS : S.mass (fun a => P a ∧ Q a) = 0 :=
      le_antisymm (hzero ▸ Dist.mass_mono hS0 fun a h => h.2)
        (hS0.mass_nonneg _)
    have hT : T.mass (fun a => P' a ∧ Q' a) = 0 :=
      le_antisymm (hzero' ▸ Dist.mass_mono hT0 fun a h => h.2)
        (hT0.mass_nonneg _)
    rw [hS, hT]
  · have hzero' : T.mass Q' ≠ 0 := hQ ▸ hzero
    have hS : S.cond P Q
        = Part.some (S.mass (fun a => P a ∧ Q a) / S.mass Q) :=
      Part.eq_some_iff.mpr ⟨hzero, rfl⟩
    have hT : T.cond P' Q'
        = Part.some (T.mass (fun a => P' a ∧ Q' a) / T.mass Q') :=
      Part.eq_some_iff.mpr ⟨hzero', rfl⟩
    rw [hS, hT] at hcond
    have hratio := Part.some_inj.mp hcond
    rw [hQ] at hratio
    have hmul := congrArg (fun r : ℝ => r * T.mass Q') hratio
    simpa [div_mul_cancel₀, hzero'] using hmul

/-- Repackage a list of the right length as a `Vector`, so that Def 3.18's
`Vector`-typed arguments can be produced from list data. -/
private def toVec {α : Type*} {n : ℕ} (l : List α) (h : l.length = n) : Vector α n :=
  Vector.ofFn fun k : Fin n => l[k.1]'(by omega)

@[simp] private theorem toVec_toList {α : Type*} {n : ℕ} (l : List α)
    (h : l.length = n) : (toVec l h).toList = l := by
  subst h
  rw [toVec, Vector.toList_ofFn]
  exact List.ofFn_getElem

/-! ### The successful-history mass -/

/-- CR18 Definition 3.18/3.20's **successful-history event** at list arguments:
the deterministic system accepts every prefix of `xs` of length at most `|ys|`
and answers it with the corresponding entry of `ys`.  This is the single event
that both the Def 3.18 kernel's numerator and its normalizer are built from
(`behavior_apply`), and — on total systems — the one that Def 3.20's
`observableBehavior` measures (`observableBehavior_zip_eq_successMass`). -/
def SuccessEvent (xs : List X) (ys : List Y) (s : PFunDDS.DDS X Y) : Prop :=
  ∀ k : Fin ys.length,
    ∃ h : xs.take (k.1 + 1) ∈ PFunDDS.dom s,
      PFunDDS.output s (xs.take (k.1 + 1)) h = ys.get k

/-- The mass of the successful-history event. -/
noncomputable def successMass (S : PFunPDS X Y) (xs : List X) (ys : List Y) :
    ℝ :=
  S.mass (SuccessEvent xs ys)

/-- **CR18 Definition 3.18 unfolded**: the behavior kernel is the conditional of
the successful-history event one step longer given the successful-history event
so far.  Definitional; stated so the `Vector` arguments never have to be
manipulated again. -/
theorem behavior_apply (S : PFunPDS X Y) (i : ℕ) (yi : Y)
    (xv : Vector X (i + 1)) (yv : Vector Y i) :
    PFunPDS.behavior S i (yi, (xv, yv))
      = Dist.cond S
          (fun s => ∃ h : xv.toList ∈ PFunDDS.dom s,
            PFunDDS.output s xv.toList h = yi)
          (SuccessEvent xv.toList yv.toList) :=
  rfl

/-- The empty answer list imposes nothing. -/
theorem successMass_nil (S : PFunPDS X Y) (xs : List X) :
    successMass S xs [] = S.weight := by
  unfold successMass SuccessEvent
  rw [Dist.mass_congr S (Q := fun _ => True)
    (fun s => iff_of_true (fun k => absurd k.2 (by simp)) trivial), Dist.mass_true]

/-- The successful-history event only reads the first `|ys|` queries, so
truncating the query list beyond that length changes nothing. -/
theorem successMass_take_of_le (S : PFunPDS X Y) (xs : List X) (ys : List Y)
    {m : ℕ} (hm : ys.length ≤ m) :
    successMass S (xs.take m) ys = successMass S xs ys := by
  unfold successMass
  refine Dist.mass_congr S fun s => forall_congr' fun k => ?_
  have hk : k.1 + 1 ≤ m := by have := k.2; omega
  rw [List.take_take, min_eq_left hk]

/-- Splitting off the last answer: the successful-history event for `ys ++ [v]`
is the event for `ys` conjoined with a single acceptance clause.  This is the
shape `behavior_apply` conditions. -/
theorem successMass_snoc (S : PFunPDS X Y) (xs : List X) (ys : List Y) (v : Y) :
    successMass S xs (ys ++ [v])
      = S.mass (fun s =>
          (∃ h : xs.take (ys.length + 1) ∈ PFunDDS.dom s,
              PFunDDS.output s (xs.take (ys.length + 1)) h = v)
            ∧ SuccessEvent xs ys s) := by
  unfold successMass SuccessEvent
  refine Dist.mass_congr S fun s => ?_
  constructor
  · intro h
    refine ⟨?_, fun k => ?_⟩
    · have hlast := h ⟨ys.length, by simp⟩
      simpa using hlast
    · have hk := h ⟨k.1, by simp⟩
      simpa [List.getElem_append_left k.2, List.get_eq_getElem] using hk
  · rintro ⟨hlast, hprev⟩ k
    have hk : k.1 < ys.length + 1 := by have := k.2; simpa using this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · have := hprev ⟨k.1, hlt⟩
      simpa [List.getElem_append_left hlt, List.get_eq_getElem] using this
    · have hval : (ys ++ [v]).get k = v := by
        simp [List.get_eq_getElem, heq]
      rw [hval]
      have hidx : k.1 = ys.length := heq
      rw [hidx]
      exact hlast

/-! ### Def 3.18 kernels determine — and are determined by — `successMass` -/

/-- Equal successful-history masses give equal Def 3.18 kernels.  No totality
and no probability normalization is needed here: `Dist.cond` reads only the two
masses. -/
theorem behaviorEq_of_successMass_eq {S T : PFunPDS X Y}
    (h : ∀ (xs : List X) (ys : List Y), ys.length ≤ xs.length →
      successMass S xs ys = successMass T xs ys) :
    PFunPDS.BehaviorEq S T := by
  unfold successMass at h
  funext i arg
  obtain ⟨yi, xv, yv⟩ := arg
  rw [behavior_apply, behavior_apply]
  have hxlen : xv.toList.length = i + 1 := by simp
  have hylen : yv.toList.length = i := by simp
  refine cond_congr_of_mass_eq ?_ ?_
  · exact h xv.toList yv.toList (by omega)
  · have hfull : xv.toList.take (yv.toList.length + 1) = xv.toList := by
      rw [List.take_of_length_le]; omega
    have hS := successMass_snoc S xv.toList yv.toList yi
    have hT := successMass_snoc T xv.toList yv.toList yi
    rw [hfull] at hS hT
    rw [← hS, ← hT]
    exact h xv.toList (yv.toList ++ [yi]) (by simp)

/-- Equal Def 3.18 kernels give equal successful-history masses.  This is CR18
eq. (3.2)'s chain rule, run as an induction on the answer list: the zero-mass
case of a conditioning prefix is handled by `mass_and_eq_of_cond_eq` rather than
excluded by a definedness hypothesis, which is why no analogue of
`cumulativeBehavior_eq_behavior_prod`'s `hdef` appears. -/
theorem successMass_eq_of_behaviorEq {S T : PFunPDS X Y}
    (hS : S.isProbDist) (hT : T.isProbDist) (h : PFunPDS.BehaviorEq S T)
    (xs : List X) (ys : List Y) (hlen : ys.length ≤ xs.length) :
    successMass S xs ys = successMass T xs ys := by
  induction ys using List.reverseRecOn with
  | nil => rw [successMass_nil, successMass_nil, hS.2, hT.2]
  | append_singleton ys v ih =>
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      have hprev : successMass S xs ys = successMass T xs ys := ih (by omega)
      -- the truncated query list, packaged as Def 3.18's `Vector` argument
      have hxv : (xs.take (ys.length + 1)).length = ys.length + 1 := by
        rw [List.length_take]; omega
      have hyv : ys.length = ys.length := rfl
      set xv : Vector X (ys.length + 1) := toVec (xs.take (ys.length + 1)) hxv
        with hxvdef
      set yv : Vector Y ys.length := toVec ys hyv with hyvdef
      have hxvl : xv.toList = xs.take (ys.length + 1) := by
        rw [hxvdef, toVec_toList]
      have hyvl : yv.toList = ys := by rw [hyvdef, toVec_toList]
      have hcond := congrFun (congrFun h ys.length) (v, (xv, yv))
      rw [behavior_apply, behavior_apply, hxvl, hyvl] at hcond
      -- the conditioning masses are the previous successful-history masses
      have hQS : S.mass (SuccessEvent (xs.take (ys.length + 1)) ys)
          = T.mass (SuccessEvent (xs.take (ys.length + 1)) ys) := by
        show successMass S (xs.take (ys.length + 1)) ys
          = successMass T (xs.take (ys.length + 1)) ys
        rw [successMass_take_of_le S xs ys (by omega),
          successMass_take_of_le T xs ys (by omega)]
        exact hprev
      have hjoint := mass_and_eq_of_cond_eq hS.1 hT.1 hQS hcond
      -- and the joint masses are the next successful-history masses
      have hself : (xs.take (ys.length + 1)).take (ys.length + 1)
          = xs.take (ys.length + 1) := by
        rw [List.take_take, min_self]
      have hSs := successMass_snoc S (xs.take (ys.length + 1)) ys v
      have hTs := successMass_snoc T (xs.take (ys.length + 1)) ys v
      rw [hself] at hSs hTs
      rw [successMass_take_of_le S xs (ys ++ [v]) (by simp)] at hSs
      rw [successMass_take_of_le T xs (ys ++ [v]) (by simp)] at hTs
      rw [hSs, hTs, hjoint]

/-! ### Def 3.20's `s⊥`-behavior is `successMass` on total systems -/

/-- On a system that accepts every nonempty history the `⊥`-completion is the
system itself, tagged with `some`: no query is ever skipped, so the deletion
pass of CR18 Def 3.3 is the identity. -/
private theorem raw_fullyDefined_of_total {s : PFunDDS.DDS X Y}
    (htot : ∀ m : List X, m ≠ [] → m ∈ PFunDDS.dom s) {l : List X} (hne : l ≠ []) :
    (PFunDDS.fullyDefined s).1 l
      = Part.some (some (PFunDDS.output s l (htot l hne))) := by
  obtain ⟨m, x, rfl⟩ : ∃ m x, l = m ++ [x] :=
    ⟨l.dropLast, l.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hfd : m ++ [x] ∈ PFunDDS.dom (PFunDDS.fullyDefined s) := by
    rw [PFunDDS.dom_fullyDefined]; simp
  rw [(Part.some_get hfd).symm]
  exact congrArg Part.some
    (PFunDDS.output_fullyDefined_append_of_mem s m x
      (by by_cases hm : m = []
          · exact Or.inr hm
          · exact Or.inl (htot m hm)) (htot _ hne))

/-- A transcript recording a `⊥` answer is impossible for a total system, so
Def 3.20's `s⊥`-behavior vanishes there. -/
theorem observableBehavior_eq_zero_of_getElem_none {S : PFunPDS X Y}
    (htot : TotalOnNonempty S) {t : List (X × Option Y)} {k : ℕ}
    (hk : k < t.length) (hnone : t[k].2 = none) : observableBehavior S t = 0 := by
  have hne : PFunDDS.transcriptInputs (t.take (k + 1)) ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    simp only [PFunDDS.transcriptInputs, List.length_map, List.length_take]
    omega
  refine Eq.trans (mass_congr_of_support S (Q := fun _ => False) fun s hs => ?_)
    (Dist.mass_eq_zero_of_forall_not S fun _ h => h)
  refine iff_of_false (fun hcons => ?_) (fun h => h)
  have hval := hcons k hk
  rw [raw_fullyDefined_of_total (fun m hm => htot s hs m hm) hne, hnone] at hval
  exact Option.some_ne_none _ (Part.some_inj.mp hval)

/-- **Where totality enters.**  On a total system Def 3.20's cumulative
`s⊥`-behavior at an all-answered transcript is exactly the successful-history
mass — the `⊥` alphabet carries no information, so CR18's Def 3.18 conditioning
throws nothing away.  This is the step the four self-destructing atoms of the
counterexample above break. -/
theorem observableBehavior_zip_eq_successMass {S : PFunPDS X Y}
    (htot : TotalOnNonempty S) (xs : List X) (ys : List Y)
    (hlen : xs.length = ys.length) :
    observableBehavior S (xs.zip (ys.map some)) = successMass S xs ys := by
  have hzlen : (xs.zip (ys.map some)).length = ys.length := by
    simp [hlen]
  refine mass_congr_of_support S fun s hs => ?_
  have htot' : ∀ m : List X, m ≠ [] → m ∈ PFunDDS.dom s := fun m hm => htot s hs m hm
  have hinputs : ∀ k : ℕ,
      PFunDDS.transcriptInputs ((xs.zip (ys.map some)).take (k + 1))
        = xs.take (k + 1) := by
    intro k
    rw [PFunDDS.transcriptInputs, List.map_take, List.map_fst_zip]
    simp [hlen]
  have hne : ∀ k : ℕ, k < ys.length → xs.take (k + 1) ≠ [] := by
    intro k hk
    refine List.ne_nil_of_length_pos ?_
    rw [List.length_take]
    omega
  constructor
  · intro hcons k
    have hk : k.1 < (xs.zip (ys.map some)).length := by rw [hzlen]; exact k.2
    have hval := hcons k.1 hk
    rw [hinputs k.1, raw_fullyDefined_of_total htot' (hne k.1 k.2)] at hval
    refine ⟨htot' _ (hne k.1 k.2), ?_⟩
    have hentry : (xs.zip (ys.map some))[k.1].2 = some (ys.get k) := by
      simp [List.getElem_zip, List.get_eq_getElem]
    rw [hentry] at hval
    exact Option.some_inj.mp (Part.some_inj.mp hval)
  · intro hsucc k hk
    rw [hzlen] at hk
    have hval := hsucc ⟨k, hk⟩
    obtain ⟨hdom, hout⟩ := hval
    rw [hinputs k, raw_fullyDefined_of_total htot' (hne k hk)]
    have hentry : ((xs.zip (ys.map some))[k]'(by rw [hzlen]; exact hk)).2
        = some (ys.get ⟨k, hk⟩) := by
      simp [List.getElem_zip, List.get_eq_getElem]
    rw [hentry, ← hout]

/-- Every all-answered transcript is a zip of its query list with its answer
list. -/
private theorem map_snd_eq_map_some {t : List (X × Option Y)}
    (h : ∀ p ∈ t, p.2 ≠ none) :
    t.map Prod.snd = (t.filterMap Prod.snd).map some := by
  induction t with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨v, hv⟩ : ∃ v, p.2 = some v := Option.ne_none_iff_exists'.mp
        (h p (by simp))
      simp only [List.map_cons, List.filterMap_cons, hv]
      rw [ih fun q hq => h q (by simp [hq])]

/-! ### The comparison theorem -/

/-- The two spellings of "the domains carry no information" agree: a law is
`TotalOnNonempty` exactly when it has the fixed domain of all nonempty
histories.  (`PFunDDS.Valid` already forces `[] ∉ dom s`, so the fixed-domain
form adds nothing.)  Recorded so the hypothesis of
`behaviorEq_iff_equivalent_of_total` can be read either way. -/
theorem totalOnNonempty_iff_hasFixedDomain (S : PFunPDS X Y) :
    TotalOnNonempty S ↔ PFunPDS.HasFixedDomain S {l : List X | l ≠ []} := by
  constructor
  · intro htot s hs
    ext l
    exact ⟨fun hl hnil => PFunDDS.empty_not_mem s (hnil ▸ hl), fun hl => htot s hs l hl⟩
  · intro hdom s hs l hl
    rw [hdom s hs]
    exact hl

/-- **The positive half of the Definition 3.18 comparison.**  On *total*
systems — every deterministic system in either support accepts every nonempty
history — CR18 Definition 3.18/3.19 behavior equality is equivalent to the
thesis's Definition 2.17 transcript equivalence.

Together with `behaviorEq_not_equivalent_counterexample` this completes the
picture: the successful-history kernel is the right notion exactly where domains
carry no information, and provably the wrong one where they do.  Both
hypotheses are needed — the counterexample's laws are probability laws, and its
atoms are precisely the non-total ones.

Not to be confused with `behavior_equivalent_iff_transcript_equivalent`, which
identifies transcript equivalence with Definition 3.20's *cumulative*
`s⊥`-behavior and needs no totality; that theorem is used here as one step. -/
theorem behaviorEq_iff_equivalent_of_total (S T : PFunPDS.Prob X Y)
    (hStot : TotalOnNonempty S.val) (hTtot : TotalOnNonempty T.val) :
    PFunPDS.BehaviorEq S.val T.val ↔ Equivalent S.val T.val := by
  rw [← behavior_equivalent_iff_transcript_equivalent S T]
  constructor
  · intro hb
    funext t
    by_cases hall : ∀ p ∈ t, p.2 ≠ none
    · have hzip : (PFunDDS.transcriptInputs t).zip
          ((t.filterMap Prod.snd).map some) = t :=
        (List.zip_of_prod rfl (map_snd_eq_map_some hall)).symm
      have hlen : (PFunDDS.transcriptInputs t).length
          = (t.filterMap Prod.snd).length := by
        have := congrArg List.length (map_snd_eq_map_some hall)
        simp only [List.length_map] at this ⊢
        simp [PFunDDS.transcriptInputs, this]
      have hSz := observableBehavior_zip_eq_successMass hStot
        (PFunDDS.transcriptInputs t) (t.filterMap Prod.snd) hlen
      have hTz := observableBehavior_zip_eq_successMass hTtot
        (PFunDDS.transcriptInputs t) (t.filterMap Prod.snd) hlen
      rw [hzip] at hSz hTz
      rw [hSz, hTz]
      exact successMass_eq_of_behaviorEq S.2 T.2 hb _ _ (le_of_eq hlen.symm)
    · obtain ⟨p, hp, hpnone⟩ : ∃ p ∈ t, p.2 = none := by
        by_contra hcontra
        exact hall fun p hp hpn => hcontra ⟨p, hp, hpn⟩
      obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hp
      rw [observableBehavior_eq_zero_of_getElem_none hStot hk (by rw [hpk]; exact hpnone),
        observableBehavior_eq_zero_of_getElem_none hTtot hk (by rw [hpk]; exact hpnone)]
  · intro hobs
    refine behaviorEq_of_successMass_eq fun xs ys hlen => ?_
    have hxlen : (xs.take ys.length).length = ys.length := by
      rw [List.length_take]; omega
    have hSz := observableBehavior_zip_eq_successMass hStot
      (xs.take ys.length) ys hxlen
    have hTz := observableBehavior_zip_eq_successMass hTtot
      (xs.take ys.length) ys hxlen
    rw [← successMass_take_of_le S.val xs ys le_rfl,
      ← successMass_take_of_le T.val xs ys le_rfl, ← hSz, ← hTz,
      congrFun hobs _]

/-- Non-vacuity of the totality hypothesis: a point law on a stateless
evaluator is total.  (A general seed-indexed family is
`CondEquiv.totalOnNonempty_fTransform_historyEvaluator`.) -/
theorem totalOnNonempty_single_functionEvaluator (f : X → Y) (c : ℝ) :
    TotalOnNonempty (Finsupp.single (PFunDDS.functionEvaluator f) c) := by
  intro s hs xs hne
  obtain rfl : s = PFunDDS.functionEvaluator f :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  exact hne

/-- Sharpness, for free: the counterexample's two laws cannot both be total —
otherwise `behaviorEq_iff_equivalent_of_total` applied to
`four_pattern_behavior_eq` would contradict `four_pattern_not_equivalent`.  The
totality hypothesis is therefore not an artifact of the proof: it is exactly
what the counterexample violates. -/
theorem four_pattern_not_both_totalOnNonempty :
    ¬ (TotalOnNonempty fourPatternSource.{v} ∧
        TotalOnNonempty fourPatternTarget.{v}) := by
  rintro ⟨hS, hT⟩
  exact four_pattern_not_equivalent
    ((behaviorEq_iff_equivalent_of_total
      ⟨fourPatternSource, four_pattern_source_nonNeg,
        four_pattern_source_has_weight_one⟩
      ⟨fourPatternTarget, four_pattern_target_nonNeg,
        four_pattern_target_has_weight_one⟩ hS hT).mp
      four_pattern_behavior_eq)

end TotalSystems

end RandomSystems.CR18.AttainmentCounterexample
