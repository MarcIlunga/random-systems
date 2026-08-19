/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TranscriptBranchDistance

/-!
# Source-bounded attainment infrastructure

This module starts the source-faithful induction lane for the hard direction of
Lanzenberger--Maurer's attainment theorem.  Its public boundary deliberately
retains all three hypotheses used by the sources:

* the query alphabet is finite (`[Fintype X]`);
* every DDS atom on both sides has one common domain `D`;
* the common domain has a uniform finite query-depth bound.

There is no varying-domain theorem here.  Observable rejection makes the
corresponding unrestricted statement false.

The page references below were checked against rendered pages of the original
PDF files, rather than against extracted text or project notes:

* `papers/LanMau20.pdf`: PDF/printed pages 11 (Definition 5: finite DDS),
  13 (Definition 8: common-domain finite PDS), 15 (Theorem 1), 16 (Lemma 6),
  and 17--18 (the induction proof and per-answer reassembly);
* `papers/thesis (1).pdf`: PDF pages 23, 25, 26, 28, and 30--33, which are
  printed thesis pages 13, 15, 16, 18, and 20--23 respectively (Definitions
  2.9, 2.14, 2.17, 2.26/2.28, Theorem 2.31, Lemma 2.33, and its proof).

In particular, the source induction is on the maximum number of answered
queries.  At a first query `x`, all atoms answer because `[x]` lies in the
common domain, and every successor has the same residual domain with one less
unit of depth.  The depth-zero theorem and the per-answer distance identity
below are the two initial endpoints consumed by that induction.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

namespace PFunDDS

/-- The residual common domain after an answered first query `x`.

The empty history is excluded because a DDS domain never contains it; a
nonempty residual history `m` is admitted exactly when `x :: m` was admitted
before the query. -/
def successorDomain (D : Set (List X)) (x : X) : Set (List X) :=
  {m | m ≠ [] ∧ x :: m ∈ D}

/-- Every deterministic atom with fixed domain `D` has the source residual
domain after an answered first query. -/
theorem successor_domain_eq_of_fixed_domain_and_answered
    {s : PFunDDS.DDS X Y} {D : Set (List X)} {x : X}
    (hs : PFunDDS.dom s = D) (hx : [x] ∈ D) :
    PFunDDS.dom (PFunDDS.DDS.successor s x) = successorDomain D x := by
  have hxs : [x] ∈ PFunDDS.dom s := hs.symm ▸ hx
  ext m
  constructor
  · intro hm
    have hne : m ≠ [] := fun h => by
      subst h
      exact PFunDDS.empty_not_mem _ hm
    exact ⟨hne, hs ▸ (mem_dom_successor_iff hxs hne).mp hm⟩
  · rintro ⟨hne, hm⟩
    exact (mem_dom_successor_iff hxs hne).mpr (hs.symm ▸ hm)

/-- The residual domain of a `(q + 1)`-bounded source domain is `q`-bounded. -/
theorem successor_domain_is_bounded_by_predecessor_of_bounded
    {D : Set (List X)} {x : X} {q : Nat}
    (hD : QBounded D (q + 1)) :
    QBounded (successorDomain D x) q := by
  intro m hm
  have hlen := hD (x :: m) hm.2
  simp only [List.length_cons] at hlen
  omega

end PFunDDS

namespace PFunPDS

/-- The exact common-domain and depth invariant carried by the source
induction.  Finiteness of the input alphabet remains an explicit typeclass
hypothesis on the public induction theorems. -/
def HaveCommonDomainAndBounded
    (S T : PFunPDS X Y) (D : Set (List X)) (q : Nat) : Prop :=
  HasFixedDomain S D ∧ HasFixedDomain T D ∧ QBounded D q

open Classical in
/-- The finite set of first `Option`-answers occurring on either side at `x`.

It is finite because a PDS has finite support; no finiteness assumption on the
answer alphabet is needed. -/
noncomputable def firstAnswerImage
    (S T : PFunPDS X Y) (x : X) : Finset (Option Y) :=
  (S.support ∪ T.support).image fun s =>
    PFunDDS.output (PFunDDS.fullyDefined s) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp)

open Classical in
/-- The finite set of queries admitted as a first query by `D`. -/
noncomputable def firstQueries [Fintype X] (D : Set (List X)) : Finset X :=
  Finset.univ.filter fun x => [x] ∈ D

open Classical in
/-- The finite set of realized proper first answers on either side.  Finiteness
comes from PDS support, not from an ambient `[Fintype Y]`. -/
noncomputable def firstAnsweredValues
    (S T : PFunPDS X Y) (x : X) : Finset Y :=
  (firstAnswerImage S T x).biUnion Option.toFinset

end PFunPDS

open Classical in
/-- Successor sampling preserves honesty.  This invariant has to be stated
explicitly now that the distribution carrier itself permits signed mass. -/
theorem successorTransform_nonNeg_of_nonNeg {S : PFunPDS X Y}
    (hS : S.NonNeg) (x : X) (y : Option Y) :
    (successorTransform S x y).NonNeg := by
  unfold successorTransform
  refine Dist.NonNeg.fTransform ?_ _
  intro s
  rw [Finsupp.filter_apply]
  split
  · exact hS s
  · exact le_rfl

open Classical in
/-- Membership in the proper-answer carrier is exactly membership of the
corresponding `some` answer in the finite `Option` answer image. -/
theorem mem_first_answered_values_iff_some_mem_first_answer_image
    {S T : PFunPDS X Y} {x : X} {v : Y} :
    v ∈ PFunPDS.firstAnsweredValues S T x ↔
      some v ∈ PFunPDS.firstAnswerImage S T x := by
  unfold PFunPDS.firstAnsweredValues
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨y, hy, hv⟩
    cases y with
    | none => simp at hv
    | some v' =>
        simp only [Option.toFinset_some, Finset.mem_singleton] at hv
        subst v'
        exact hy
  · intro hv
    exact ⟨some v, hv, by simp⟩

/-- A finite first-query carrier exposes exactly the singleton histories in
its defining domain. -/
theorem mem_first_queries_iff_singleton_mem_domain [Fintype X]
    {D : Set (List X)} {x : X} :
    x ∈ PFunPDS.firstQueries D ↔ [x] ∈ D := by
  classical
  simp [PFunPDS.firstQueries]

open Classical in
/-- A distribution with zero total weight is zero. -/
theorem distribution_eq_zero_of_weight_eq_zero {A : Type*}
    {S : Dist A} (hS : S.NonNeg) (h : S.weight = 0) : S = 0 := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra ha
  have hle : S a ≤ S.weight := by
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.single_le_sum (fun a' _ => hS a')
      (Finsupp.mem_support_iff.mpr ha)
  rw [h] at hle
  exact ha (le_antisymm hle (hS a))

open Classical in
/-- Pushing a finite-support distribution through a constant map produces one
atom carrying the original weight. -/
theorem distribution_pushforward_const_eq_single_weight {A B : Type*}
    (b : B) (S : Dist A) :
    Dist.fTransform (fun _ => b) S = Finsupp.single b S.weight := by
  refine Finsupp.ext fun z => ?_
  rw [Dist.fTransform_apply_eq_mass, Finsupp.single_apply]
  by_cases h : b = z
  · rw [if_pos h]
    subst z
    refine Eq.trans (Dist.mass_congr S fun _ => iff_of_true rfl trivial)
      (Dist.mass_true S)
  · rw [if_neg h]
    exact Dist.mass_eq_zero_of_forall_not S fun _ => h

/-- At horizon zero the transcript law contains only the empty transcript and
the PDS weight. -/
theorem transcript_distribution_zero_eq_single_empty_weight
    (S : PFunPDS X Y) (e : PFunDDS.DDE X Y) :
    transcriptDist S e 0 = Finsupp.single [] S.weight := by
  show Dist.fTransform (fun _ => ([] : List (X × Option Y))) S = _
  exact distribution_pushforward_const_eq_single_weight _ S

/-- An environment that stalls initially produces the empty transcript at
every horizon. -/
theorem transcript_eq_empty_of_environment_stalls_at_start
    {e : PFunDDS.DDE X Y} (he : e [] = none)
    (s : PFunDDS.DDS X Y) :
    ∀ n, PFunDDS.transcript s e n = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [transcript_succ_stall (by rw [ih]; exact he), ih]

open Classical in
/-- A PDS observed by an initially stalled environment exposes only its
weight, at every horizon. -/
theorem transcript_distribution_stall_eq_single_empty_weight
    {e : PFunDDS.DDE X Y} (he : e [] = none)
    (S : PFunPDS X Y) (n : Nat) :
    transcriptDist S e n = Finsupp.single [] S.weight := by
  show Dist.fTransform _ S = _
  have hfun : (fun s : PFunDDS.DDS X Y => PFunDDS.transcript s e n) =
      fun _ => ([] : List (X × Option Y)) := by
    funext s
    exact transcript_eq_empty_of_environment_stalls_at_start he s n
  rw [hfun]
  exact distribution_pushforward_const_eq_single_weight _ S

open Classical in
/-- If every support atom rejects `x`, the observable `none` successor is the
original PDS, exactly as required by CR18 skip semantics. -/
theorem successor_none_eq_self_of_support_rejects
    {S : PFunPDS X Y} {x : X}
    (h : ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s) :
    successorTransform S x none = S := by
  rw [successorTransform_none_eq_filter]
  refine Finsupp.ext fun s => ?_
  rw [Finsupp.filter_apply]
  by_cases hs : s ∈ S.support
  · rw [if_pos (h s hs)]
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact ite_self 0

open Classical in
/-- An answer absent from the support answer image has a zero successor
subdistribution. -/
theorem successor_eq_zero_of_answer_not_mem_first_answer_image
    {S : PFunPDS X Y} {x : X} {y : Option Y}
    (hy : y ∉ S.support.image (fun s =>
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp))) :
    successorTransform S x y = 0 := by
  unfold successorTransform
  rw [show S.filter (fun s =>
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y) = 0 by
    apply Finsupp.ext
    intro s
    rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    split
    · rename_i hs
      by_cases hmem : s ∈ S.support
      · exact False.elim (hy (Finset.mem_image.mpr ⟨s, hmem, hs⟩))
      · exact Finsupp.notMem_support_iff.mp hmem
    · rfl]
  simp [Dist.fTransform]

open Classical in
/-- Every successor pair is eligible for the induction hypothesis at one less
depth.  The theorem deliberately exposes the source restrictions in its name
and retains `[Fintype X]`, even though this local domain calculation itself
does not enumerate `X`. -/
theorem successor_pair_has_common_domain_and_one_less_bound_of_finite_common_domain_and_bounded
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)} {q : Nat}
    {x : X} (h : PFunPDS.HaveCommonDomainAndBounded S T D (q + 1))
    (hx : [x] ∈ D) (y : Option Y) :
    PFunPDS.HaveCommonDomainAndBounded
      (successorTransform S x y) (successorTransform T x y)
      (PFunDDS.successorDomain D x) q := by
  rcases h with ⟨hS, hT, hD⟩
  refine ⟨?_, ?_,
    PFunDDS.successor_domain_is_bounded_by_predecessor_of_bounded hD⟩
  · intro s' hs'
    unfold successorTransform at hs'
    obtain ⟨s, hs, rfl⟩ := Dist.mem_support_fTransform _ _ hs'
    have hsS : s ∈ S.support := by
      have hsFilter : s ∈ S.support.filter (fun s =>
          PFunDDS.output (PFunDDS.fullyDefined s) [x]
            (by rw [PFunDDS.dom_fullyDefined]; simp) = y) := by
        rw [← Finsupp.support_filter]
        exact hs
      exact (Finset.mem_filter.mp hsFilter).1
    exact PFunDDS.successor_domain_eq_of_fixed_domain_and_answered
      (hS s hsS) hx
  · intro t' ht'
    unfold successorTransform at ht'
    obtain ⟨t, ht, rfl⟩ := Dist.mem_support_fTransform _ _ ht'
    have htT : t ∈ T.support := by
      have htFilter : t ∈ T.support.filter (fun t =>
          PFunDDS.output (PFunDDS.fullyDefined t) [x]
            (by rw [PFunDDS.dom_fullyDefined]; simp) = y) := by
        rw [← Finsupp.support_filter]
        exact ht
      exact (Finset.mem_filter.mp htFilter).1
    exact PFunDDS.successor_domain_eq_of_fixed_domain_and_answered
      (hT t htT) hx

/-- A deterministic DDS whose domain is zero-bounded is the empty DDS. -/
theorem deterministic_system_eq_empty_of_domain_bounded_zero
    (s : PFunDDS.DDS X Y) (h : QBounded (PFunDDS.dom s) 0) :
    s = PFunDDS.DDS.empty := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · intro hy
    have hdom : l ∈ PFunDDS.dom s := Part.dom_iff_mem.mpr ⟨y, hy⟩
    have hlen := h l hdom
    have hl : l = [] :=
      List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst l
    exact (PFunDDS.empty_not_mem s hdom).elim
  · intro hy
    simp [PFunDDS.DDS.empty] at hy

open Classical in
/-- A fixed-domain distribution at source depth zero is concentrated on the
empty DDS, with its original (possibly non-unit) weight. -/
theorem distribution_eq_single_empty_of_fixed_domain_and_bounded_zero
    {S : PFunPDS X Y} {D : Set (List X)}
    (hS : PFunPDS.HasFixedDomain S D) (hD : QBounded D 0) :
    S = Finsupp.single PFunDDS.DDS.empty S.weight := by
  apply Finsupp.eq_single_iff.mpr
  constructor
  · intro s hs
    rw [Finset.mem_singleton]
    apply deterministic_system_eq_empty_of_domain_bounded_zero s
    intro l hl
    exact hD l ((hS s hs) ▸ hl)
  · rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    have hsub : S.support ⊆ {PFunDDS.DDS.empty} := by
      intro s hs
      rw [Finset.mem_singleton]
      apply deterministic_system_eq_empty_of_domain_bounded_zero s
      intro l hl
      exact hD l ((hS s hs) ▸ hl)
    rcases Finset.subset_singleton_iff.mp hsub with hsupp | hsupp
    · have hnot : PFunDDS.DDS.empty ∉ S.support := by
        rw [hsupp]
        simp
      rw [hsupp, Finset.sum_empty, Finsupp.notMem_support_iff.mp hnot]
    · rw [hsupp, Finset.sum_singleton]

/-- The one-sided statistical distance between two real masses on one atom. -/
theorem delta_single_same_eq_max_sub_zero {A : Type*}
    (a : A) (p q : ℝ) (hq : 0 ≤ q) :
    δ (Finsupp.single a p) (Finsupp.single a q) = max (p - q) 0 := by
  unfold δ
  rw [Finsupp.sum_single_index]
  · rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_same]
    exact max_eq_right (sub_nonpos.mpr hq)

open Classical in
/-- The source depth-zero static distance is exactly the weight difference. -/
theorem delta_eq_weight_sub_weight_of_finite_common_domain_and_bounded_zero
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)}
    (hTnn : T.NonNeg)
    (h : PFunPDS.HaveCommonDomainAndBounded S T D 0) :
    δ S T = max (S.weight - T.weight) 0 := by
  rcases h with ⟨hS, hT, hD⟩
  let p := S.weight
  let q := T.weight
  have hSeq : S = Finsupp.single PFunDDS.DDS.empty p := by
    simpa [p] using
      distribution_eq_single_empty_of_fixed_domain_and_bounded_zero hS hD
  have hTeq : T = Finsupp.single PFunDDS.DDS.empty q := by
    simpa [q] using
      distribution_eq_single_empty_of_fixed_domain_and_bounded_zero hT hD
  calc
    δ S T = δ (Finsupp.single PFunDDS.DDS.empty p)
        (Finsupp.single PFunDDS.DDS.empty q) := congrArg₂ δ hSeq hTeq
    _ = max (p - q) 0 :=
      delta_single_same_eq_max_sub_zero _ _ _ hTnn.weight_nonneg
    _ = max (S.weight - T.weight) 0 := rfl

/-- Pushing a one-atom empty-system distribution to transcripts yields one
transcript atom with the same weight. -/
theorem transcript_distribution_single_empty_eq_single_transcript
    (e : PFunDDS.DDE X Y) (n : Nat) (p : ℝ) :
    transcriptDist (Finsupp.single PFunDDS.DDS.empty p) e n =
      Finsupp.single
        (PFunDDS.transcript
          (PFunDDS.DDS.empty (X := X) (Y := Y)) e n) p := by
  simp [transcriptDist, Dist.fTransform]

open Classical in
/-- The exact source induction base: at common-domain depth zero, optimal
transcript advantage already equals the static distance of the given pair. -/
theorem optimal_advantage_eq_static_distance_of_finite_common_domain_and_bounded_zero
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)}
    (hTnn : T.NonNeg)
    (h : PFunPDS.HaveCommonDomainAndBounded S T D 0) :
    Adv S T = (δ S T : Real) := by
  rcases h with ⟨hS, hT, hD⟩
  let p := S.weight
  let q := T.weight
  have hSeq : S = Finsupp.single PFunDDS.DDS.empty p := by
    simpa [p] using
      distribution_eq_single_empty_of_fixed_domain_and_bounded_zero hS hD
  have hTeq : T = Finsupp.single PFunDDS.DDS.empty q := by
    simpa [q] using
      distribution_eq_single_empty_of_fixed_domain_and_bounded_zero hT hD
  have hvalue : ∀ (e : PFunDDS.DDE X Y) (n : Nat),
      (δ (transcriptDist S e n) (transcriptDist T e n) : Real) =
        (δ S T : Real) := by
    intro e n
    rw [hSeq, hTeq,
      transcript_distribution_single_empty_eq_single_transcript,
      transcript_distribution_single_empty_eq_single_transcript]
    rw [delta_single_same_eq_max_sub_zero _ _ _ hTnn.weight_nonneg,
      delta_single_same_eq_max_sub_zero _ _ _ hTnn.weight_nonneg]
  unfold Adv
  have hset : {a : Real | ∃ (e : PFunDDS.DDE X Y) (n : Nat),
      a = (δ (transcriptDist S e n) (transcriptDist T e n) : Real)} =
      {(δ S T : Real)} := by
    ext a
    constructor
    · rintro ⟨e, n, rfl⟩
      exact Set.mem_singleton_iff.mpr (hvalue e n)
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact ⟨fun _ => none, 0, (hvalue (fun _ => none) 0).symm⟩
  rw [hset, csSup_singleton]

open Classical in
/-- At a query admitted by the common domain, the finite first-answer image
contains no observable rejection. -/
theorem none_not_mem_first_answer_image_of_common_domain_and_answered
    {S T : PFunPDS X Y} {D : Set (List X)} {x : X}
    (hS : PFunPDS.HasFixedDomain S D)
    (hT : PFunPDS.HasFixedDomain T D) (hx : [x] ∈ D) :
    none ∉ PFunPDS.firstAnswerImage S T x := by
  intro hnone
  obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hnone
  have hsdom : PFunDDS.dom s = D := by
    rcases Finset.mem_union.mp hs with hsS | hsT
    · exact hS s hsS
    · exact hT s hsT
  have hmem : [x] ∈ PFunDDS.dom s := hsdom.symm ▸ hx
  exact (output_fullyDefined_eq_none_iff.mp hans) hmem

open Classical in
/-- At an answered common-domain query, the finite `Option`-answer image is
exactly the image of its finite proper-answer carrier. -/
theorem first_answer_image_eq_image_some_of_common_domain_and_answered
    {S T : PFunPDS X Y} {D : Set (List X)} {x : X}
    (hS : PFunPDS.HasFixedDomain S D)
    (hT : PFunPDS.HasFixedDomain T D) (hx : [x] ∈ D) :
    PFunPDS.firstAnswerImage S T x =
      (PFunPDS.firstAnsweredValues S T x).image some := by
  ext y
  cases y with
  | none =>
      simp only [Finset.mem_image]
      constructor
      · exact fun h =>
          (none_not_mem_first_answer_image_of_common_domain_and_answered
            hS hT hx h).elim
      · rintro ⟨v, -, h⟩
        cases h
  | some v =>
      rw [Finset.mem_image]
      constructor
      · intro hv
        exact ⟨v,
          mem_first_answered_values_iff_some_mem_first_answer_image.mpr hv,
          rfl⟩
      · rintro ⟨v', hv', h⟩
        cases Option.some.inj h
        exact mem_first_answered_values_iff_some_mem_first_answer_image.mp hv'

open Classical in
/-- Summing the weights of the finitely many successor fibers over any
finite cover of the realized first-answer image recovers the original
subdistribution weight. -/
theorem sum_weight_successors_eq_weight_of_answer_image_subset
    {S : PFunPDS X Y} {x : X} {ys : Finset (Option Y)}
    (hcover : S.support.image (fun s =>
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp)) ⊆ ys) :
    ∑ y ∈ ys, (successorTransform S x y).weight = S.weight := by
  rw [← Dist.mass_true S]
  simp only [weight_successorTransform, Dist.mass, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  let ans := PFunDDS.output (PFunDDS.fullyDefined s) [x]
    (by rw [PFunDDS.dom_fullyDefined]; simp)
  have hans : ans ∈ ys := hcover (Finset.mem_image_of_mem _ hs)
  rw [Finset.sum_eq_single_of_mem ans hans]
  · simp [ans]
  · intro y hy hne
    rw [if_neg]
    exact fun h => hne h.symm

open Classical in
/-- For an answered common-domain query, the proper successor branches on
one side have total mass equal to that side's original weight.  No common
mass between the two sides is assumed. -/
theorem sum_weight_successor_some_eq_weight_of_common_domain_and_answered
    {S T : PFunPDS X Y} {D : Set (List X)} {x : X}
    (hS : PFunPDS.HasFixedDomain S D)
    (hT : PFunPDS.HasFixedDomain T D) (hx : [x] ∈ D) :
    ∑ v ∈ PFunPDS.firstAnsweredValues S T x,
        (successorTransform S x (some v)).weight = S.weight := by
  have hcover : S.support.image (fun s =>
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp)) ⊆
      PFunPDS.firstAnswerImage S T x := by
    intro y hy
    exact Finset.mem_image.mpr <| by
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨s, Finset.mem_union_left _ hs, rfl⟩
  have hsum := sum_weight_successors_eq_weight_of_answer_image_subset hcover
  rw [first_answer_image_eq_image_some_of_common_domain_and_answered
    hS hT hx, Finset.sum_image] at hsum
  · exact hsum
  · intro a _ b _ hab
    exact Option.some.inj hab

open Classical in
/-- The first-step transcript decomposition may be summed over any finite
answer carrier covering the realized answer image; the additional fibers are
zero. -/
theorem transcript_distribution_successor_eq_sum_over_answer_cover
    {S : PFunPDS X Y} {e : PFunDDS.DDE X Y} {x : X} {n : Nat}
    {ys : Finset (Option Y)} (he : e [] = some x)
    (hcover : S.support.image (fun s =>
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp)) ⊆ ys) :
    transcriptDist S e (n + 1) =
      ∑ y ∈ ys, Dist.fTransform (fun t => (x, y) :: t)
        (transcriptDist (successorTransform S x y)
          (PFunDDS.DDE.successor e y) n) := by
  rw [transcriptDist_successor S e he n]
  apply Finset.sum_subset hcover
  intro y hy hyimage
  have hzero : successorTransform S x y = 0 :=
    successor_eq_zero_of_answer_not_mem_first_answer_image hyimage
  rw [hzero]
  simp [transcriptDist, Dist.fTransform]

open Classical in
/-- The union answer image of two systems is a common finite carrier for the
first-step transcript decomposition of either side. -/
theorem transcript_distribution_successor_eq_sum_over_first_answer_image
    {S T : PFunPDS X Y} {e : PFunDDS.DDE X Y} {x : X} {n : Nat}
    (he : e [] = some x) :
    transcriptDist S e (n + 1) =
      ∑ y ∈ PFunPDS.firstAnswerImage S T x,
        Dist.fTransform (fun t => (x, y) :: t)
          (transcriptDist (successorTransform S x y)
            (PFunDDS.DDE.successor e y) n) := by
  apply transcript_distribution_successor_eq_sum_over_answer_cover he
  intro y hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr
    ⟨s, Finset.mem_union_left _ hs, rfl⟩

open Classical in
/-- If every support atom rejects a query, every proper-answer successor at
that query is zero. -/
theorem successor_some_eq_zero_of_support_rejects
    {S : PFunPDS X Y} {x : X} {v : Y}
    (h : ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s) :
    successorTransform S x (some v) = 0 := by
  apply successor_eq_zero_of_answer_not_mem_first_answer_image
  rintro hy
  obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hy
  have hnone := output_fullyDefined_eq_none_iff.mpr (h s hs)
  rw [hnone] at hans
  cases hans

open Classical in
/-- If every support atom answers a query, its observable rejection successor
is zero. -/
theorem successor_none_eq_zero_of_support_answers
    {S : PFunPDS X Y} {x : X}
    (h : ∀ s ∈ S.support, [x] ∈ PFunDDS.dom s) :
    successorTransform S x none = 0 := by
  apply successor_eq_zero_of_answer_not_mem_first_answer_image
  rintro hy
  obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hy
  exact (output_fullyDefined_eq_none_iff.mp hans) (h s hs)

open Classical in
/-- A fixed-domain source is reconstructed, up to transcript equivalence,
from its weight, all answered first-query successors, and rejection outside
the fixed domain.  The finite-input hypothesis is retained because this is a
boundary lemma for the finite-source induction. -/
private theorem equivalent_of_equal_weight_and_successor_equivalence_of_finite_fixed_domain
    [Fintype X] {R S : PFunPDS X Y} {D : Set (List X)}
    (hRnn : R.NonNeg) (hSnn : S.NonNeg)
    (hweight : R.weight = S.weight)
    (hS : PFunPDS.HasFixedDomain S D)
    (hRreject : ∀ {x : X}, [x] ∉ D →
      ∀ r ∈ R.support, [x] ∉ PFunDDS.dom r)
    (hsucc : ∀ {x : X}, [x] ∈ D → ∀ y : Option Y,
      Equivalent (successorTransform R x y)
        (successorTransform S x y)) :
    Equivalent R S := by
  intro e n
  induction n generalizing e with
  | zero =>
      rw [transcript_distribution_zero_eq_single_empty_weight,
        transcript_distribution_zero_eq_single_empty_weight, hweight]
  | succ n ih =>
      rcases he : e [] with _ | x
      · rw [transcript_distribution_stall_eq_single_empty_weight he,
          transcript_distribution_stall_eq_single_empty_weight he,
          hweight]
      · have hSreject : [x] ∉ D →
            ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s := by
          intro hx s hs hdom
          exact hx ((hS s hs) ▸ hdom)
        have hbranchweight : ∀ y : Option Y,
            (successorTransform R x y).weight =
              (successorTransform S x y).weight := by
          intro y
          by_cases hx : [x] ∈ D
          · exact weight_eq_of_equivalent (hsucc hx y)
          · cases y with
            | none =>
                rw [successor_none_eq_self_of_support_rejects
                    (hRreject hx),
                  successor_none_eq_self_of_support_rejects
                    (hSreject hx), hweight]
            | some v =>
                rw [successor_some_eq_zero_of_support_rejects
                    (hRreject hx),
                  successor_some_eq_zero_of_support_rejects
                    (hSreject hx)]
        have himage : R.support.image (fun r =>
              PFunDDS.output (PFunDDS.fullyDefined r) [x]
                (by rw [PFunDDS.dom_fullyDefined]; simp)) =
            S.support.image (fun s =>
              PFunDDS.output (PFunDDS.fullyDefined s) [x]
                (by rw [PFunDDS.dom_fullyDefined]; simp)) := by
          ext y
          rw [first_answer_mem_support_image_iff_successor_weight_ne_zero hRnn,
            first_answer_mem_support_image_iff_successor_weight_ne_zero hSnn,
            hbranchweight y]
        rw [transcriptDist_successor R e he n,
          transcriptDist_successor S e he n, himage]
        refine Finset.sum_congr rfl fun y _ => congrArg
          (Dist.fTransform fun t => (x, y) :: t) ?_
        by_cases hx : [x] ∈ D
        · exact hsucc hx y (PFunDDS.DDE.successor e y) n
        · cases y with
          | none =>
              rw [successor_none_eq_self_of_support_rejects
                  (hRreject hx),
                successor_none_eq_self_of_support_rejects
                  (hSreject hx)]
              exact ih (PFunDDS.DDE.successor e none)
          | some v =>
              rw [successor_some_eq_zero_of_support_rejects
                  (hRreject hx),
                successor_some_eq_zero_of_support_rejects
                  (hSreject hx)]

/-- A deterministic system admitting no singleton query is the empty system:
prefix closure would otherwise expose the first query of any nonempty domain
history. -/
theorem deterministic_system_eq_empty_of_no_singleton_domain
    (s : PFunDDS.DDS X Y)
    (h : ∀ x : X, [x] ∉ PFunDDS.dom s) :
    s = PFunDDS.DDS.empty := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · intro hy
    have hdom : l ∈ PFunDDS.dom s := Part.dom_iff_mem.mpr ⟨y, hy⟩
    cases l with
    | nil => exact (PFunDDS.empty_not_mem s hdom).elim
    | cons x m =>
        have hsingleton : [x] ∈ PFunDDS.dom s :=
          s.2.2 (by exact ⟨m, by simp⟩) (by simp) hdom
        exact (h x hsingleton).elim
  · intro hy
    simp [PFunDDS.DDS.empty] at hy

open Classical in
/-- A distribution whose support atoms accept no singleton query is
concentrated on the empty deterministic system, with the same total mass. -/
theorem distribution_eq_single_empty_of_support_rejects_every_query
    {S : PFunPDS X Y}
    (h : ∀ s ∈ S.support, ∀ x : X, [x] ∉ PFunDDS.dom s) :
    S = Finsupp.single PFunDDS.DDS.empty S.weight := by
  apply Finsupp.eq_single_iff.mpr
  constructor
  · intro s hs
    rw [Finset.mem_singleton]
    exact deterministic_system_eq_empty_of_no_singleton_domain s (h s hs)
  · rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    have hsub : S.support ⊆ {PFunDDS.DDS.empty} := by
      intro s hs
      rw [Finset.mem_singleton]
      exact deterministic_system_eq_empty_of_no_singleton_domain s (h s hs)
    rcases Finset.subset_singleton_iff.mp hsub with hsupp | hsupp
    · have hnot : PFunDDS.DDS.empty ∉ S.support := by
        rw [hsupp]
        simp
      rw [hsupp, Finset.sum_empty, Finsupp.notMem_support_iff.mp hnot]
    · rw [hsupp, Finset.sum_singleton]

/-- Internal induction package: representatives preserving both original
transcript classes and their separate masses, together with one finite-
horizon environment whose transcript distance is their static distance. -/
private structure BoundedAttainmentWitness
    (S T : PFunPDS X Y) (q : Nat) where
  left : PFunPDS X Y
  right : PFunPDS X Y
  left_nonNeg : left.NonNeg
  right_nonNeg : right.NonNeg
  left_equivalent : Equivalent left S
  right_equivalent : Equivalent right T
  left_weight : left.weight = S.weight
  right_weight : right.weight = T.weight
  environment : PFunDDS.DDE X Y
  delta_eq_transcript :
    (δ left right : Real) =
      (δ (transcriptDist S environment q)
        (transcriptDist T environment q) : Real)

open Classical in
/-- Base package for the bounded-depth induction. -/
private theorem exists_bounded_attainment_witness_zero_of_finite_common_domain
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PFunPDS.HaveCommonDomainAndBounded S T D 0) :
    Nonempty (BoundedAttainmentWitness S T 0) := by
  refine ⟨{
    left := S
    right := T
    left_nonNeg := hSnn
    right_nonNeg := hTnn
    left_equivalent := fun _ _ => rfl
    right_equivalent := fun _ _ => rfl
    left_weight := rfl
    right_weight := rfl
    environment := fun _ => none
    delta_eq_transcript := ?_
  }⟩
  rw [transcript_distribution_zero_eq_single_empty_weight,
    transcript_distribution_zero_eq_single_empty_weight,
    delta_single_same_eq_max_sub_zero _ _ _ hTnn.weight_nonneg]
  exact_mod_cast
    delta_eq_weight_sub_weight_of_finite_common_domain_and_bounded_zero hTnn h

open Classical in
set_option maxHeartbeats 2000000 in
/-- The source induction: finite input carrier, one common domain, and a
uniform bound on answered queries suffice to construct representatives whose
static distance is exposed by one bounded transcript experiment. -/
private theorem exists_bounded_attainment_witness_of_finite_common_domain_and_bounded
    [Fintype X] :
    ∀ (q : Nat) (S T : PFunPDS X Y) (D : Set (List X)),
      S.NonNeg → T.NonNeg →
      PFunPDS.HaveCommonDomainAndBounded S T D q →
        Nonempty (BoundedAttainmentWitness S T q) := by
  intro q
  induction q with
  | zero =>
      intro S T D hSnn hTnn h
      exact
        exists_bounded_attainment_witness_zero_of_finite_common_domain hSnn hTnn h
  | succ q ih =>
      intro S T D hSnn hTnn h
      let C := PFunPDS.firstQueries D
      have hS : PFunPDS.HasFixedDomain S D := h.1
      have hT : PFunPDS.HasFixedDomain T D := h.2.1
      have hxdom : ∀ {x : X}, x ∈ C → [x] ∈ D := by
        intro x hx
        exact mem_first_queries_iff_singleton_mem_domain.mp
          (by simpa [C] using hx)
      by_cases hC : C.Nonempty
      · let branch : (x : {x : X // x ∈ C}) → (v : Y) →
            BoundedAttainmentWitness
              (successorTransform S x.1 (some v))
              (successorTransform T x.1 (some v)) q :=
          fun x v => Classical.choice <| ih
            (successorTransform S x.1 (some v))
            (successorTransform T x.1 (some v))
            (PFunDDS.successorDomain D x.1)
            (successorTransform_nonNeg_of_nonNeg hSnn _ _)
            (successorTransform_nonNeg_of_nonNeg hTnn _ _)
            (successor_pair_has_common_domain_and_one_less_bound_of_finite_common_domain_and_bounded
              h (hxdom x.property) (some v))
        let vs : X → Finset Y := fun x =>
          PFunPDS.firstAnsweredValues S T x
        let Bs : X → Y → PFunPDS X Y := fun x v =>
          if hx : x ∈ C then (branch ⟨x, hx⟩ v).left else 0
        let Bt : X → Y → PFunPDS X Y := fun x v =>
          if hx : x ∈ C then (branch ⟨x, hx⟩ v).right else 0
        have hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight = S.weight := by
          intro i hi
          calc
            ∑ v ∈ vs i, (Bs i v).weight =
                ∑ v ∈ vs i, (successorTransform S i (some v)).weight := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [show Bs i v = (branch ⟨i, hi⟩ v).left by
                simp [Bs, hi]]
              exact (branch ⟨i, hi⟩ v).left_weight
            _ = S.weight := by
              exact sum_weight_successor_some_eq_weight_of_common_domain_and_answered
                hS hT (hxdom hi)
        have hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight = T.weight := by
          intro i hi
          calc
            ∑ v ∈ vs i, (Bt i v).weight =
                ∑ v ∈ vs i, (successorTransform T i (some v)).weight := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [show Bt i v = (branch ⟨i, hi⟩ v).right by
                simp [Bt, hi]]
              exact (branch ⟨i, hi⟩ v).right_weight
            _ = T.weight := by
              simpa [vs, PFunPDS.firstAnsweredValues,
                PFunPDS.firstAnswerImage, Finset.union_comm] using
                (sum_weight_successor_some_eq_weight_of_common_domain_and_answered
                  hT hS (hxdom hi))
        have hBsnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg := by
          intro i hi v hv
          rw [show Bs i v = (branch ⟨i, hi⟩ v).left by simp [Bs, hi]]
          exact (branch ⟨i, hi⟩ v).left_nonNeg
        have hBtnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg := by
          intro i hi v hv
          rw [show Bt i v = (branch ⟨i, hi⟩ v).right by simp [Bt, hi]]
          exact (branch ⟨i, hi⟩ v).right_nonNeg
        let joint : FiniteClassJointWitness (fun x : X => x) C vs Bs Bt
            S.weight T.weight := Classical.choice <|
          exists_finite_class_joint_witness_of_common_side_weights
            (fun x : X => x) C hC (fun i _ => ⟨i, rfl⟩) vs Bs Bt
              S.weight T.weight hBsnn hBtnn hwS hwT
        have hleft : Equivalent joint.left S := by
          apply
            equivalent_of_equal_weight_and_successor_equivalence_of_finite_fixed_domain
              joint.left_nonNeg hSnn joint.left_weight hS
          · intro x hx
            apply joint.left_rejects_of_class_not_mem
            intro hxin
            exact hx (hxdom (by simpa using hxin))
          · intro x hx y
            have hxin : x ∈ C := by
              simpa [C] using
                (mem_first_queries_iff_singleton_mem_domain.mpr hx)
            cases y with
            | none =>
                rw [joint.left_successor_none (x := x) (by simpa using hxin),
                  successor_none_eq_zero_of_support_answers
                    (fun s hs => (hS s hs).symm ▸ hx)]
                exact fun _ _ => rfl
            | some v =>
                by_cases hv : v ∈ vs x
                · rw [joint.left_successor_of_mem (x := x) (v := v)
                      (by simpa using hxin) hv,
                    show Bs x v = (branch ⟨x, hxin⟩ v).left by
                      simp [Bs, hxin]]
                  exact (branch ⟨x, hxin⟩ v).left_equivalent
                · rw [joint.left_successor_of_not_mem (x := x) (v := v)
                      (by simpa using hxin) hv]
                  have hzero : successorTransform S x (some v) = 0 := by
                    apply successor_eq_zero_of_answer_not_mem_first_answer_image
                    intro himage
                    apply hv
                    apply mem_first_answered_values_iff_some_mem_first_answer_image.mpr
                    obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp himage
                    exact Finset.mem_image.mpr
                      ⟨s, Finset.mem_union_left _ hs, hans⟩
                  rw [hzero]
                  exact fun _ _ => rfl
        have hright : Equivalent joint.right T := by
          apply
            equivalent_of_equal_weight_and_successor_equivalence_of_finite_fixed_domain
              joint.right_nonNeg hTnn joint.right_weight hT
          · intro x hx
            apply joint.right_rejects_of_class_not_mem
            intro hxin
            exact hx (hxdom (by simpa using hxin))
          · intro x hx y
            have hxin : x ∈ C := by
              simpa [C] using
                (mem_first_queries_iff_singleton_mem_domain.mpr hx)
            cases y with
            | none =>
                rw [joint.right_successor_none (x := x) (by simpa using hxin),
                  successor_none_eq_zero_of_support_answers
                    (fun t ht => (hT t ht).symm ▸ hx)]
                exact fun _ _ => rfl
            | some v =>
                by_cases hv : v ∈ vs x
                · rw [joint.right_successor_of_mem (x := x) (v := v)
                      (by simpa using hxin) hv,
                    show Bt x v = (branch ⟨x, hxin⟩ v).right by
                      simp [Bt, hxin]]
                  exact (branch ⟨x, hxin⟩ v).right_equivalent
                · rw [joint.right_successor_of_not_mem (x := x) (v := v)
                      (by simpa using hxin) hv]
                  have hzero : successorTransform T x (some v) = 0 := by
                    apply successor_eq_zero_of_answer_not_mem_first_answer_image
                    intro himage
                    apply hv
                    apply mem_first_answered_values_iff_some_mem_first_answer_image.mpr
                    obtain ⟨t, ht, hans⟩ := Finset.mem_image.mp himage
                    exact Finset.mem_image.mpr
                      ⟨t, Finset.mem_union_right _ ht, hans⟩
                  rw [hzero]
                  exact fun _ _ => rfl
        let x₀ := joint.chosen
        have hx₀ : x₀ ∈ C := joint.chosen_mem
        let e : PFunDDS.DDE X Y := fun ys =>
          match ys with
          | [] => some x₀
          | some v :: rest =>
              if hv : v ∈ vs x₀ then
                (branch ⟨x₀, hx₀⟩ v).environment rest
              else none
          | none :: _ => none
        have he : e [] = some x₀ := rfl
        have hsuccessor_environment : ∀ {v : Y}, v ∈ vs x₀ →
            PFunDDS.DDE.successor e (some v) =
              (branch ⟨x₀, hx₀⟩ v).environment := by
          intro v hv
          funext rest
          simp [PFunDDS.DDE.successor, e, hv]
        have htranscriptS : transcriptDist S e (q + 1) =
            ∑ v ∈ vs x₀,
              Dist.fTransform (fun t => (x₀, some v) :: t)
                (transcriptDist (successorTransform S x₀ (some v))
                  (branch ⟨x₀, hx₀⟩ v).environment q) := by
          rw [transcript_distribution_successor_eq_sum_over_first_answer_image
              (T := T) he,
            first_answer_image_eq_image_some_of_common_domain_and_answered
              hS hT (hxdom hx₀), Finset.sum_image]
          · refine Finset.sum_congr rfl fun v hv => ?_
            rw [hsuccessor_environment hv]
          · intro a _ b _ hab
            exact Option.some.inj hab
        have htranscriptT : transcriptDist T e (q + 1) =
            ∑ v ∈ vs x₀,
              Dist.fTransform (fun t => (x₀, some v) :: t)
                (transcriptDist (successorTransform T x₀ (some v))
                  (branch ⟨x₀, hx₀⟩ v).environment q) := by
          rw [transcript_distribution_successor_eq_sum_over_first_answer_image
              (S := T) (T := S) he,
            show PFunPDS.firstAnswerImage T S x₀ =
                PFunPDS.firstAnswerImage S T x₀ by
              simp [PFunPDS.firstAnswerImage, Finset.union_comm],
            first_answer_image_eq_image_some_of_common_domain_and_answered
              hS hT (hxdom hx₀), Finset.sum_image]
          · refine Finset.sum_congr rfl fun v hv => ?_
            rw [hsuccessor_environment hv]
          · intro a _ b _ hab
            exact Option.some.inj hab
        have hbranch_distance :
            (δ (∑ v ∈ vs x₀,
                  Dist.fTransform (fun t => (x₀, some v) :: t)
                    (transcriptDist (successorTransform S x₀ (some v))
                      (branch ⟨x₀, hx₀⟩ v).environment q))
                (∑ v ∈ vs x₀,
                  Dist.fTransform (fun t => (x₀, some v) :: t)
                    (transcriptDist (successorTransform T x₀ (some v))
                      (branch ⟨x₀, hx₀⟩ v).environment q)) : Real) =
              ∑ v ∈ vs x₀,
                (δ (transcriptDist (successorTransform S x₀ (some v))
                      (branch ⟨x₀, hx₀⟩ v).environment q)
                    (transcriptDist (successorTransform T x₀ (some v))
                      (branch ⟨x₀, hx₀⟩ v).environment q) : Real) := by
          have hδ :=
            delta_sum_cons_pushforwards_eq_sum_of_deltas_of_finite_answers
              x₀ ((vs x₀).image some)
              (fun y => match y with
                | none => 0
                | some v => transcriptDist
                    (successorTransform S x₀ (some v))
                    (branch ⟨x₀, hx₀⟩ v).environment q)
              (fun y => match y with
                | none => 0
                | some v => transcriptDist
                    (successorTransform T x₀ (some v))
                    (branch ⟨x₀, hx₀⟩ v).environment q)
              (by
                intro y hy
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
                exact transcriptDist_nonNeg
                  (successorTransform_nonNeg_of_nonNeg hTnn x₀ (some v))
                  (branch ⟨x₀, hx₀⟩ v).environment q)
          rw [Finset.sum_image, Finset.sum_image, Finset.sum_image] at hδ
          · exact_mod_cast hδ
          · intro a _ b _ hab
            exact Option.some.inj hab
          · intro a _ b _ hab
            exact Option.some.inj hab
          · intro a _ b _ hab
            exact Option.some.inj hab
        refine ⟨{
          left := joint.left
          right := joint.right
          left_nonNeg := joint.left_nonNeg
          right_nonNeg := joint.right_nonNeg
          left_equivalent := hleft
          right_equivalent := hright
          left_weight := joint.left_weight
          right_weight := joint.right_weight
          environment := e
          delta_eq_transcript := ?_
        }⟩
        calc
          (δ joint.left joint.right : Real) =
              ∑ v ∈ vs x₀, (δ (Bs x₀ v) (Bt x₀ v) : Real) := by
            simpa [x₀] using joint.delta_eq_selected_sum
          _ = ∑ v ∈ vs x₀,
                (δ (branch ⟨x₀, hx₀⟩ v).left
                  (branch ⟨x₀, hx₀⟩ v).right : Real) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp [Bs, Bt, hx₀]
          _ = ∑ v ∈ vs x₀,
                (δ (transcriptDist (successorTransform S x₀ (some v))
                      (branch ⟨x₀, hx₀⟩ v).environment q)
                    (transcriptDist (successorTransform T x₀ (some v))
                      (branch ⟨x₀, hx₀⟩ v).environment q) : Real) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            exact (branch ⟨x₀, hx₀⟩ v).delta_eq_transcript
          _ = (δ (transcriptDist S e (q + 1))
                (transcriptDist T e (q + 1)) : Real) := by
            rw [htranscriptS, htranscriptT, hbranch_distance]
      · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
        have hxnot : ∀ x : X, [x] ∉ D := by
          intro x hx
          have hxin : x ∈ C := by
            simpa [C] using
              (mem_first_queries_iff_singleton_mem_domain.mpr hx)
          rw [hCempty] at hxin
          simp at hxin
        have hSreject : ∀ s ∈ S.support, ∀ x : X,
            [x] ∉ PFunDDS.dom s := by
          intro s hs x hdom
          exact hxnot x ((hS s hs) ▸ hdom)
        have hTreject : ∀ t ∈ T.support, ∀ x : X,
            [x] ∉ PFunDDS.dom t := by
          intro t ht x hdom
          exact hxnot x ((hT t ht) ▸ hdom)
        have hSeq :=
          distribution_eq_single_empty_of_support_rejects_every_query hSreject
        have hTeq :=
          distribution_eq_single_empty_of_support_rejects_every_query hTreject
        let e : PFunDDS.DDE X Y := fun _ => none
        have he : e [] = none := rfl
        refine ⟨{
          left := S
          right := T
          left_nonNeg := hSnn
          right_nonNeg := hTnn
          left_equivalent := fun _ _ => rfl
          right_equivalent := fun _ _ => rfl
          left_weight := rfl
          right_weight := rfl
          environment := e
          delta_eq_transcript := ?_
        }⟩
        rw [transcript_distribution_stall_eq_single_empty_weight he,
          transcript_distribution_stall_eq_single_empty_weight he,
          delta_single_same_eq_max_sub_zero _ _ _ hTnn.weight_nonneg]
        have hstatic : δ S T = max (S.weight - T.weight) 0 := by
          calc
            δ S T = δ (Finsupp.single PFunDDS.DDS.empty S.weight)
                (Finsupp.single PFunDDS.DDS.empty T.weight) :=
              congrArg₂ δ hSeq hTeq
            _ = max (S.weight - T.weight) 0 :=
              delta_single_same_eq_max_sub_zero _ _ _ hTnn.weight_nonneg
        exact_mod_cast hstatic

open Classical in
/-- Source-bounded attainment (Lanzenberger--Maurer Theorem 1 / thesis
Theorem 2.31, hard direction).  For a finite query alphabet, one common
domain, and a uniform bound on answered queries, there are transcript-
equivalent representatives whose separate masses are preserved and whose
static statistical distance equals optimal transcript advantage. -/
theorem exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)} {q : Nat}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PFunPDS.HaveCommonDomainAndBounded S T D q) :
    ∃ S' T' : PFunPDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' S ∧ Equivalent T' T ∧
      S'.weight = S.weight ∧ T'.weight = T.weight ∧
      (δ S' T' : Real) = Adv S T := by
  obtain ⟨witness⟩ :=
    exists_bounded_attainment_witness_of_finite_common_domain_and_bounded
      q S T D hSnn hTnn h
  refine ⟨witness.left, witness.right, witness.left_nonNeg,
    witness.right_nonNeg, witness.left_equivalent,
    witness.right_equivalent, witness.left_weight, witness.right_weight, ?_⟩
  apply le_antisymm
  · rw [witness.delta_eq_transcript]
    exact le_csSup (bddAbove_adv_set hSnn hTnn)
      ⟨witness.environment, q, rfl⟩
  · refine csSup_le ⟨_, (fun _ => none), 0, rfl⟩ ?_
    rintro a ⟨e, n, rfl⟩
    rw [← witness.left_equivalent e n,
      ← witness.right_equivalent e n]
    have hdata := δ_fTransform_le
      (fun s => PFunDDS.transcript s e n) witness.left witness.right_nonNeg
    simp only [transcriptDist]
    exact_mod_cast hdata

open Classical in
/-- Source-bounded equality between equivalence-class distance and optimal
transcript advantage.  This characterization is intentionally independent
of the quotient metric used by the AC instance. -/
theorem class_distance_eq_optimal_advantage_of_finite_common_domain_and_bounded
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)} {q : Nat}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PFunPDS.HaveCommonDomainAndBounded S T D q) :
    Δ S T = Adv S T := by
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', hSweight, hTweight, hdelta⟩ :=
    exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded
      hSnn hTnn h
  apply le_antisymm
  · rw [← hdelta]
    unfold Δ
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro a ⟨R, U, hR, hU, _hR, _hU, rfl⟩
      exact δ_nonneg R U
    · exact ⟨S', T', hS'nn, hT'nn, hS', hT', rfl⟩
  · exact optimal_advantage_le_class_distance hSnn hTnn

open Classical in
/-- The source one-node distance identity.  Reassembling the finite answer
classes at an answered common-domain query has distance equal to the sum of
the successor-pair distances.  This is the directly consumed distance step of
the bounded-depth induction; it makes no unrestricted varying-domain claim. -/
theorem delta_reassembled_successors_eq_sum_of_successor_deltas_of_finite_common_domain_and_bounded
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)} {q : Nat}
    (hTnn : T.NonNeg)
    {x : X} (h : PFunPDS.HaveCommonDomainAndBounded S T D (q + 1))
    (hx : [x] ∈ D) :
    δ (∑ y ∈ PFunPDS.firstAnswerImage S T x,
          prependTransform (successorTransform S x y) x y)
        (∑ y ∈ PFunPDS.firstAnswerImage S T x,
          prependTransform (successorTransform T x y) x y) =
      ∑ y ∈ PFunPDS.firstAnswerImage S T x,
        δ (successorTransform S x y) (successorTransform T x y) := by
  rcases h with ⟨hS, hT, hD⟩
  apply δ_sum_prependTransform
  · intro y
    exact successorTransform_nonNeg_of_nonNeg hTnn x y
  · intro hnone
    exact (none_not_mem_first_answer_image_of_common_domain_and_answered
      hS hT hx hnone).elim
  · intro hnone
    exact (none_not_mem_first_answer_image_of_common_domain_and_answered
      hS hT hx hnone).elim

end RandomSystems.CR18
