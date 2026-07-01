/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.FixedQuery

/-!
# Law-level adaptive transcript-law bridge

This module contains the generic CR18 bridge from fixed-query pointwise
transcript-law ratios to arbitrary law-level environments.

The proof is CR18 Lemma 3.2: a transcript law factors as a system factor times
an environment factor.  A fixed-query ratio controls the system factor, and the
arbitrary environment contributes the same nonnegative factor to both sides.

Migration note: this is support infrastructure, not the public H-technique
surface.  New application statements should use the law-level endpoints in
`NextGen.Migration.HTechnique.SecurityDefs`; this file remains build-checked as
the reusable CR18 factorization bridge behind those endpoints.
-/

noncomputable section

open scoped NNReal
open scoped RandomSystems.CR18

namespace RandomSystems
namespace CR18

universe u v w z

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
An exact-`q` CR18 distinguisher/winner view is a `q`-query-total deterministic
environment, so it is admissible in the thesis-style transcript-advantage
supremum. -/
theorem PFunPDE.DDEKQueryTotal_of_queriesExactly
    (E : PFunDDS.DDE X Y) {q : Nat} (hQ : QueriesExactly E q) :
    PFunPDE.DDEKQueryTotal E q := by
  intro ys hlen
  have hsome : (E (ys.map some)).isSome := hQ.1 (ys.map some) (by simpa using hlen)
  cases hE : E (ys.map some) with
  | none => simp [hE] at hsome
  | some x => exact ⟨x, rfl⟩

/-- **Operational transcript/readout bridge; candidate for upstream.**
If the transcript-prefix rectangle event holds for a concrete sample of the
system/environment random variables, then Maurer's operational transcript
recurrence for that sampled deterministic pair has exactly that prefix. Totality
is not a premise here: the rectangle event already contains the concrete system
outputs and environment queries for every round. -/
theorem PFunPDE.transcript_of_transcriptJointEvent
    {Ω₁ : Type w} {Ω₂ : Type z}
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) (ω : Ω₁ × Ω₂) {q : Nat}
    (t : PFunPDE.TranscriptPrefix X Y q)
    (ht : PFunPDE.transcriptJointEvent S E t ω) :
    PFunDDS.transcriptInputs (PFunDDS.transcript (S ω.1) (E ω.2) q) = t.1.toList ∧
      PFunDDS.transcriptOutputs (PFunDDS.transcript (S ω.1) (E ω.2) q) =
        t.2.toList.map some := by
  rcases ht with ⟨htS, htE⟩
  let s := S ω.1
  let e := E ω.2
  change PFunDDS.transcriptInputs (PFunDDS.transcript s e q) = t.1.toList ∧
    PFunDDS.transcriptOutputs (PFunDDS.transcript s e q) = t.2.toList.map some
  have hprefix : ∀ n, n ≤ q →
      PFunDDS.transcriptInputs (PFunDDS.transcript s e n) = t.1.toList.take n ∧
        PFunDDS.transcriptOutputs (PFunDDS.transcript s e n) =
          (t.2.toList.take n).map some := by
    intro n hn
    induction n with
    | zero =>
        simp [PFunDDS.transcript, PFunDDS.transcriptInputs, PFunDDS.transcriptOutputs]
    | succ n ih =>
        have hnk : n < q := Nat.lt_of_succ_le hn
        obtain ⟨ihx, ihy⟩ := ih (Nat.le_of_lt hnk)
        have hfire :
            e (PFunDDS.transcriptOutputs (PFunDDS.transcript s e n)) =
              some (t.1.get ⟨n, hnk⟩) := by
          rw [ihy]
          dsimp [e]
          simpa using htE n hnk
        have hx_succ : t.1.toList.take (n + 1) =
            t.1.toList.take n ++ [t.1.get ⟨n, hnk⟩] := by
          rw [← List.take_concat_get' t.1.toList n
            (by simpa [List.Vector.toList_length] using hnk)]
          congr 1
        have hy_succ : t.2.toList.take (n + 1) =
            t.2.toList.take n ++ [t.2.get ⟨n, hnk⟩] := by
          rw [← List.take_concat_get' t.2.toList n
            (by simpa [List.Vector.toList_length] using hnk)]
          congr 1
        have hraw :
            s.1 (t.1.toList.take (n + 1)) = Part.some (t.2.get ⟨n, hnk⟩) := by
          simpa [PFunPDS.funView] using htS n hnk
        have hdom : t.1.toList.take (n + 1) ∈ PFunDDS.dom s := by
          change (s.1 (t.1.toList.take (n + 1))).Dom
          rw [hraw]
          simp
        have hl : t.1.toList.take n ∈ PFunDDS.dom s ∨ t.1.toList.take n = [] := by
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · right
            subst hn0
            simp
          · left
            have hpre : t.1.toList.take n <+: t.1.toList.take (n + 1) := by
              rw [hx_succ]
              exact List.prefix_append _ _
            have hne : t.1.toList.take n ≠ [] := by
              have : 0 < (t.1.toList.take n).length := by
                rw [List.length_take, List.Vector.toList_length]
                omega
              exact List.ne_nil_of_length_pos this
            exact PFunDDS.prefix_closed s hpre hne hdom
        have hnext : t.1.toList.take n ++ [t.1.get ⟨n, hnk⟩] ∈ PFunDDS.dom s := by
          rw [← hx_succ]
          exact hdom
        have hnext' :
            PFunDDS.transcriptInputs (PFunDDS.transcript s e n) ++ [t.1.get ⟨n, hnk⟩] ∈
              PFunDDS.dom s := by
          rw [ihx]
          exact hnext
        have hl' :
            PFunDDS.transcriptInputs (PFunDDS.transcript s e n) ∈ PFunDDS.dom s ∨
              PFunDDS.transcriptInputs (PFunDDS.transcript s e n) = [] := by
          rw [ihx]
          exact hl
        have hout_s :
            PFunDDS.output s (t.1.toList.take (n + 1)) hdom =
              t.2.get ⟨n, hnk⟩ := by
          have hsome :
              s.1 (t.1.toList.take (n + 1)) =
                Part.some (PFunDDS.output s (t.1.toList.take (n + 1)) hdom) :=
            (Part.some_get hdom).symm
          exact Part.some_inj.mp (hsome.symm.trans hraw)
        have hout :
            PFunDDS.output (PFunDDS.fullyDefined s)
                (PFunDDS.transcriptInputs (PFunDDS.transcript s e n) ++ [t.1.get ⟨n, hnk⟩])
                (by
                  rw [PFunDDS.dom_fullyDefined]
                  simp) =
              some (t.2.get ⟨n, hnk⟩) := by
          rw [PFunDDS.output_fullyDefined_append_of_mem s _ _ hl' hnext',
            PFunDDS.output_congr s (by rw [ihx]; exact hx_succ.symm) hnext' hdom,
            hout_s]
        rw [transcript_succ_fire hfire]
        constructor
        · rw [transcriptInputs_append, ihx]
          exact hx_succ.symm
        · rw [transcriptOutputs_append, ihy, hy_succ, List.map_append]
          simp only [List.map_cons, List.map_nil]
          rw [hout]
  have hfull := hprefix q (le_refl q)
  have hxfull : t.1.toList.take q = t.1.toList := by
    rw [List.take_of_length_le]
    simp [List.Vector.toList_length]
  have hyfull : t.2.toList.take q = t.2.toList := by
    rw [List.take_of_length_le]
    simp [List.Vector.toList_length]
  constructor
  · simpa [hxfull] using hfull.1
  · simpa [hyfull] using hfull.2

/-- **Exact-query verdicts are transcript events; candidate for upstream.**
For a point distinguisher that makes exactly `q` queries, its CR18 verdict
probability against a law-level PDS is exactly the mass of the corresponding
accepting event in the deterministic length-`q` transcript distribution. The
only system-side premise is the meaningful support-totality needed to guarantee
that every support system realizes a length-`q` concrete transcript. -/
theorem verdictProb_single_eq_deterministicTranscriptDist_mass_of_queriesExactly
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (d : PFunDDS.DDD X Y)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q)
    (hS : S.KStepTotal q) :
    verdictProb (Finsupp.single d (1 : NNReal)) S.val =
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S (PFunDDS.ddToDDE d)).mass
        (fun t => d.val (t.2.toList.map some) = Sum.inr true) := by
  classical
  let accept : PFunPDE.TranscriptPrefix X Y q → Prop :=
    fun t => d.val (t.2.toList.map some) = Sum.inr true
  have hleft :
      verdictProb (Finsupp.single d (1 : NNReal)) S.val =
        S.val.mass (fun s => PFunDDS.verdict d s) := by
    unfold verdictProb GamePerf.winProb Dist.mass
    rw [Finsupp.sum_single_index]
    · refine Finsupp.sum_congr fun s _ => ?_
      by_cases hv : PFunDDS.verdict d s <;> simp [hv]
    · simp
  have hright :
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S (PFunDDS.ddToDDE d)).mass
          accept =
        S.val.mass (fun s =>
          ∃ t : PFunPDE.TranscriptPrefix X Y q,
            PFunPDE.transcriptJointEvent
              ((fun s : PFunDDS.DDS X Y => s) :
                PFunPDS.RV (PFunDDS.DDS X Y) X Y)
              ((fun _ : PUnit.{1} => PFunDDS.ddToDDE d) : PFunPDE.RV PUnit.{1} X Y)
              t (s, PUnit.unit) ∧ accept t) := by
    unfold PFunPDS.Prob.deterministicTranscriptDist
      PFunPDE.deterministicTranscriptLawDist
      PFunPDE.deterministicTranscriptLaw
    rw [PFunPDE.transcriptLawDist_mass_eq_mass_exists_jointEvent]
    rw [Dist.prodProbDist_val]
    rw [Dist.mass_prod_unitProbDist_right]
  rw [hleft, hright]
  refine mass_congr_support S.val fun s hs => ?_
  constructor
  · intro hv
    have hSunit : PFunPDS.RV.KStepTotal
        ((fun _ : PUnit.{1} => s) : PFunPDS.RV PUnit.{1} X Y) q := by
      intro _ xs hne hlen
      exact hS s hs xs hne hlen
    have hEunit : PFunPDE.RV.KQueryTotal
        ((fun _ : PUnit.{1} => PFunDDS.ddToDDE d) : PFunPDE.RV PUnit.{1} X Y) q := by
      intro _ ys hlen
      exact PFunPDE.DDEKQueryTotal_of_queriesExactly (PFunDDS.ddToDDE d) hQ ys hlen
    obtain ⟨t, ht⟩ := PFunPDE.transcriptJointEvent_exists_of_total
      ((fun _ : PUnit.{1} => s) : PFunPDS.RV PUnit.{1} X Y)
      ((fun _ : PUnit.{1} => PFunDDS.ddToDDE d) : PFunPDE.RV PUnit.{1} X Y)
      hSunit hEunit (PUnit.unit, PUnit.unit)
    have ht_id :
        PFunPDE.transcriptJointEvent
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y)
          ((fun _ : PUnit.{1} => PFunDDS.ddToDDE d) : PFunPDE.RV PUnit.{1} X Y)
          t (s, PUnit.unit) := by
      simpa [PFunPDS.funView] using ht
    refine ⟨t, ht_id, ?_⟩
    have hproj := PFunPDE.transcript_of_transcriptJointEvent
      ((fun _ : PUnit.{1} => s) : PFunPDS.RV PUnit.{1} X Y)
      ((fun _ : PUnit.{1} => PFunDDS.ddToDDE d) : PFunPDE.RV PUnit.{1} X Y)
      (PUnit.unit, PUnit.unit) t ht
    have hvq := (PFunDDS.verdict_iff_at_exact d s q hQ).mp hv
    change d.val (t.2.toList.map some) = Sum.inr true
    rw [← hproj.2]
    exact hvq
  · rintro ⟨t, ht, hacc⟩
    have hproj := PFunPDE.transcript_of_transcriptJointEvent
      ((fun s : PFunDDS.DDS X Y => s) :
        PFunPDS.RV (PFunDDS.DDS X Y) X Y)
      ((fun _ : PUnit.{1} => PFunDDS.ddToDDE d) : PFunPDE.RV PUnit.{1} X Y)
      (s, PUnit.unit) t ht
    apply (PFunDDS.verdict_iff_at_exact d s q hQ).mpr
    rw [hproj.2]
    exact hacc

/-- **Singleton exact-query distinguishing is bounded by adaptive transcript advantage.**
This is the point-distinguisher leaf used to lift CR18 distinguishing to the
thesis-style transcript supremum. -/
theorem advantage_single_le_adaptiveTranscriptAdvantage_of_queriesExactly
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) (d : PFunDDS.DDD X Y)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q) :
    advantage (Finsupp.single d (1 : NNReal)) S.val T.val ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T := by
  classical
  let E : PFunPDE.QQueryEnvironment X Y q :=
    ⟨PFunDDS.ddToDDE d, PFunPDE.DDEKQueryTotal_of_queriesExactly (PFunDDS.ddToDDE d) hQ⟩
  let accept : PFunPDE.TranscriptPrefix X Y q → Prop :=
    fun t => d.val (t.2.toList.map some) = Sum.inr true
  have hSverdict :
      verdictProb (Finsupp.single d (1 : NNReal)) S.val =
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1).mass accept := by
    simpa [E, accept] using
      verdictProb_single_eq_deterministicTranscriptDist_mass_of_queriesExactly
        (q := q) S d hQ hS
  have hTverdict :
      verdictProb (Finsupp.single d (1 : NNReal)) T.val =
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1).mass accept := by
    simpa [E, accept] using
      verdictProb_single_eq_deterministicTranscriptDist_mass_of_queriesExactly
        (q := q) T d hQ hT
  have hmass :
      (((PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1).mass accept : ℝ) -
        ((PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1).mass accept : ℝ)) ≤
        (RandomSystems.statDist
          (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1)
          (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1) : ℝ) :=
    RandomSystems.mass_sub_mass_le_statDist
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1)
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1)
      accept
  have hEprob : PFunPDE.Prob.KQueryTotal (PFunPDE.Prob.ofDDE E.1) q :=
    PFunPDE.Prob.ofDDE_KQueryTotal E.1 E.2
  have hSw :
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1).weight = 1 := by
    rw [← PFunPDS.Prob.transcriptDist_ofDDE (q := q) S E.1]
    exact PFunPDS.Prob.transcriptDist_weight_eq_one_of_total
      (q := q) S (PFunPDE.Prob.ofDDE E.1) hS hEprob
  have hTw :
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1).weight = 1 := by
    rw [← PFunPDS.Prob.transcriptDist_ofDDE (q := q) T E.1]
    exact PFunPDS.Prob.transcriptDist_weight_eq_one_of_total
      (q := q) T (PFunPDE.Prob.ofDDE E.1) hT hEprob
  unfold advantage
  rw [hTverdict, hSverdict]
  calc
    (((PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1).mass accept : ℝ) -
        ((PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1).mass accept : ℝ))
        ≤ (RandomSystems.statDist
            (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1)
            (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1) : ℝ) := hmass
    _ = (RandomSystems.statDist
            (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1)
            (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1) : ℝ) := by
          rw [RandomSystems.statDist_symm_of_eq_weight
            (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1)
            (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1)
            (by rw [hTw, hSw])]
    _ ≤ PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T :=
          PFunPDS.Prob.deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
            (q := q) S T E

/-- **Linearity of distinguisher verdict probability; candidate for upstream.**
Randomizing the distinguisher is the weighted mixture of the corresponding
point-distinguisher verdict probabilities. -/
theorem verdictProb_eq_sum_single
    (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y) :
    verdictProb D S =
      D.sum fun d dp => dp * verdictProb (Finsupp.single d (1 : NNReal)) S := by
  simp [verdictProb, GamePerf.winProb, Finsupp.mul_sum]

/-- **Linearity of signed distinguishing advantage; candidate for upstream.**
The CR18 signed advantage of a randomized distinguisher is the weighted mixture
of the signed advantages of its point distinguishers. -/
theorem advantage_eq_sum_single
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y) :
    advantage D S T =
      D.sum fun d dp => (dp : ℝ) * advantage (Finsupp.single d (1 : NNReal)) S T := by
  unfold advantage
  rw [verdictProb_eq_sum_single D T, verdictProb_eq_sum_single D S]
  simp [Finsupp.sum, NNReal.coe_sum, Finset.sum_sub_distrib, mul_sub]

/-- **Exact-query randomized distinguishing is bounded by adaptive transcript
advantage.**
This lifts the point-distinguisher transcript bridge to arbitrary CR18
probability distributions over exact-`q` distinguishers. -/
theorem advantage_le_adaptiveTranscriptAdvantage_of_queriesExactly
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) (D : Dist (PFunDDS.DDD X Y))
    (hD : D.isProbDist)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) q)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q) :
    advantage D S.val T.val ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T := by
  let B := PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T
  calc
    advantage D S.val T.val
        = D.sum (fun d dp =>
            (dp : ℝ) * advantage (Finsupp.single d (1 : NNReal)) S.val T.val) :=
          advantage_eq_sum_single D S.val T.val
    _ ≤ D.sum (fun _ dp => (dp : ℝ) * B) := by
          unfold Finsupp.sum
          apply Finset.sum_le_sum
          intro d hd
          exact mul_le_mul_of_nonneg_left
            (advantage_single_le_adaptiveTranscriptAdvantage_of_queriesExactly
              (q := q) S T d (hQ d hd) hS hT)
            (NNReal.coe_nonneg _)
    _ = (D.sum fun _ dp => (dp : ℝ)) * B := by
          rw [← Finsupp.sum_mul]
    _ = B := by
          have hsumNN : D.sum (fun _ dp => dp) = 1 := by
            rw [← Dist.weight_eq_finsupp_sum]
            exact hD
          have hsum : D.sum (fun _ dp => (dp : ℝ)) = 1 := by
            simpa [Finsupp.sum, NNReal.coe_sum] using congrArg (fun x : NNReal => (x : ℝ)) hsumNN
          rw [hsum, one_mul]

/-- **DDS-level query-filter evaluation; candidate for upstream.**
For histories of length at most `q`, `[q]s` has exactly the same concrete
partial-function evaluations as `s`. -/
theorem PFunDDS.filterQueries_apply_eq_some_iff
    (q : Nat) (s : PFunDDS.DDS X Y) {xs : List X} {y : Y}
    (hlen : xs.length ≤ q) :
    (PFunDDS.filterQueries q s).1 xs = Part.some y ↔ s.1 xs = Part.some y := by
  constructor
  · intro h
    have hdom : (s.1 xs).Dom := (Part.eq_some_iff.mp h).1.1
    have hget : (s.1 xs).get hdom = y := (Part.eq_some_iff.mp h).2
    exact Part.eq_some_iff.mpr ⟨hdom, hget⟩
  · intro h
    have hdom : (s.1 xs).Dom := (Part.eq_some_iff.mp h).1
    have hget : (s.1 xs).get hdom = y := (Part.eq_some_iff.mp h).2
    exact Part.eq_some_iff.mpr ⟨⟨hdom, hlen⟩, hget⟩

/-- **Query filters preserve law-level `q`-step totality; candidate for upstream.**
If every support system answers all nonempty histories of length at most `q`,
then the `[q]`-filtered law is still total for those `q` transcript steps. -/
theorem PFunPDS.Prob.KStepTotal_filterQueries_of_KStepTotal
    (S : PFunPDS.Prob X Y) {q : Nat} (hS : PFunPDS.Prob.KStepTotal S q) :
    PFunPDS.Prob.KStepTotal
      (⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩ :
        PFunPDS.Prob X Y) q := by
  intro s hs xs hne hlen
  change s ∈ (PFunPDS.filterQueries q S.val).support at hs
  unfold PFunPDS.filterQueries at hs
  obtain ⟨s₀, hs₀, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  obtain ⟨y, hy⟩ := hS s₀ hs₀ xs hne hlen
  refine ⟨y, ?_⟩
  have hdom : (s₀.1 xs).Dom := by
    rw [hy]
    simp
  have hget : (s₀.1 xs).get hdom = y :=
    Part.some_inj.mp ((Part.some_get hdom).trans hy)
  apply Part.eq_some_iff.mpr
  exact ⟨⟨hdom, hlen⟩, hget⟩

/-- **Length-`q` deterministic transcript laws ignore the `[q]` filter; candidate
for upstream.**
The filter `[q]` changes only histories longer than `q`, so it is invisible to
the length-`q` transcript distribution against any deterministic environment. -/
theorem PFunPDS.Prob.deterministicTranscriptDist_filterQueries_eq
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y) :
    PFunPDS.Prob.deterministicTranscriptDist (q := q)
        (⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩ :
          PFunPDS.Prob X Y) E =
      PFunPDS.Prob.deterministicTranscriptDist (q := q) S E := by
  ext t
  simp only [PFunPDS.Prob.deterministicTranscriptDist,
    PFunPDE.deterministicTranscriptLawDist_apply,
    PFunPDE.deterministicTranscriptLaw]
  rw [PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor]
  unfold PFunPDE.transcriptSystemFactor PFunPDS.filterQueries
  rw [Dist.mass_fTransform]
  have hsys :
      S.val.mass
          (fun s =>
            PFunPDE.transcriptSystemEvent
              ((fun s : PFunDDS.DDS X Y => s) :
                PFunPDS.RV (PFunDDS.DDS X Y) X Y)
              t.1 t.2 (PFunDDS.filterQueries q s)) =
        S.val.mass
          (PFunPDE.transcriptSystemEvent
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            t.1 t.2) := by
    apply Dist.mass_congr
    intro s
    constructor
    · intro h i hi
      exact (PFunDDS.filterQueries_apply_eq_some_iff q s
        (by
          rw [List.length_take, List.Vector.toList_length]
          omega)).mp (h i hi)
    · intro h i hi
      exact (PFunDDS.filterQueries_apply_eq_some_iff q s
        (by
          rw [List.length_take, List.Vector.toList_length]
          omega)).mpr (h i hi)
  rw [hsys]

/-- **Filtered law transcript advantage is bounded by base law transcript
advantage; candidate for upstream.**
Because length-`q` deterministic transcript laws are unchanged by `[q]`, the
thesis-style adaptive transcript supremum for filtered laws is a subexpression
of the base-law supremum. -/
theorem PFunPDS.Prob.adaptiveTranscriptAdvantage_filterQueries_le
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩ :
          PFunPDS.Prob X Y)
        (⟨⌈q⌉ T.val, (PFunPDS.isProbDist_filterQueries_iff q T.val).mpr T.property⟩ :
          PFunPDS.Prob X Y) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T := by
  unfold PFunPDS.Prob.adaptiveTranscriptAdvantage
  refine RandomSystems.sSup_image_univ_le_sSup_image_univ_of_forall_exists
    (fun E : PFunPDE.QQueryEnvironment X Y q =>
      (RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist (q := q)
          (⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩ :
            PFunPDS.Prob X Y) E.1)
        (PFunPDS.Prob.deterministicTranscriptDist (q := q)
          (⟨⌈q⌉ T.val, (PFunPDS.isProbDist_filterQueries_iff q T.val).mpr T.property⟩ :
            PFunPDS.Prob X Y) E.1) : ℝ))
    (fun E : PFunPDE.QQueryEnvironment X Y q =>
      (RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1)
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1) : ℝ))
    (PFunPDS.Prob.adaptiveTranscriptAdvantage_image_bddAbove (q := q) S T)
    (by
      intro E
      exact_mod_cast (zero_le (RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1)
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1))))
    ?_
  intro E
  refine ⟨E, ?_⟩
  change
    (RandomSystems.statDist
      (PFunPDS.Prob.deterministicTranscriptDist (q := q)
        (⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩ :
          PFunPDS.Prob X Y) E.1)
      (PFunPDS.Prob.deterministicTranscriptDist (q := q)
        (⟨⌈q⌉ T.val, (PFunPDS.isProbDist_filterQueries_iff q T.val).mpr T.property⟩ :
          PFunPDS.Prob X Y) E.1) : ℝ) =
    (RandomSystems.statDist
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1)
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) T E.1) : ℝ)
  rw [PFunPDS.Prob.deterministicTranscriptDist_filterQueries_eq (q := q) S E.1,
    PFunPDS.Prob.deterministicTranscriptDist_filterQueries_eq (q := q) T E.1]

/-- **CR18/thesis filtered-law advantage bridge; candidate for upstream.**
The raw CR18 filtered distinguishing advantage is bounded by the thesis-style
adaptive transcript advantage of the filtered laws. The proof is the CR18
finite-query normalization shell plus the exact-query randomized-distinguisher
transcript bridge above. -/
theorem maxAdvantage_filterQueries_le_filtered_adaptiveTranscriptAdvantage
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y)
    (hS : PFunPDS.Prob.KStepTotal S q) (hT : PFunPDS.Prob.KStepTotal T q)
    (hNorm : DeltaFilteredFiniteQueryNormalization q S.val T.val) :
    (Δ(⌈q⌉ S.val, ⌈q⌉ T.val) : ℝ) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        ⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩
        ⟨⌈q⌉ T.val, (PFunPDS.isProbDist_filterQueries_iff q T.val).mpr T.property⟩ := by
  let Sf : PFunPDS.Prob X Y :=
    ⟨⌈q⌉ S.val, (PFunPDS.isProbDist_filterQueries_iff q S.val).mpr S.property⟩
  let Tf : PFunPDS.Prob X Y :=
    ⟨⌈q⌉ T.val, (PFunPDS.isProbDist_filterQueries_iff q T.val).mpr T.property⟩
  have hSf : PFunPDS.Prob.KStepTotal Sf q := by
    simpa [Sf] using PFunPDS.Prob.KStepTotal_filterQueries_of_KStepTotal S hS
  have hTf : PFunPDS.Prob.KStepTotal Tf q := by
    simpa [Tf] using PFunPDS.Prob.KStepTotal_filterQueries_of_KStepTotal T hT
  change (Δ(Sf.val, Tf.val) : ℝ) ≤
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) Sf Tf
  exact maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact
    q S.val T.val
    (PFunPDS.Prob.adaptiveTranscriptAdvantage_nonneg (q := q)
      Sf Tf)
    hNorm
    (by
      intro D hD hQ
      exact advantage_le_adaptiveTranscriptAdvantage_of_queriesExactly
        (q := q) Sf Tf D hD hQ hSf hTf)

/-- **CR18/thesis advantage bridge; candidate for upstream.**
The raw CR18 filtered distinguishing advantage is bounded by the thesis-style
adaptive transcript advantage of the base laws. The `[q]` filters are invisible
to length-`q` transcript distributions, so the filtered-law bridge above
transfers to the base-law supremum. -/
theorem maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y)
    (hS : PFunPDS.Prob.KStepTotal S q) (hT : PFunPDS.Prob.KStepTotal T q)
    (hNorm : DeltaFilteredFiniteQueryNormalization q S.val T.val) :
    (Δ(⌈q⌉ S.val, ⌈q⌉ T.val) : ℝ) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T := by
  exact le_trans
    (maxAdvantage_filterQueries_le_filtered_adaptiveTranscriptAdvantage
      (q := q) S T hS hT hNorm)
    (PFunPDS.Prob.adaptiveTranscriptAdvantage_filterQueries_le (q := q) S T)

/-- Law-level fixed-query pointwise transcript-law ratios transfer to arbitrary
law-level CR18 environments. -/
theorem transcriptLaw_ratio_of_fixedQuery_ratio_law
    (R I : PFunPDS.Prob X Y)
    (E : PFunPDE.Prob X Y)
    (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (t : PFunPDE.TranscriptPrefix X Y q),
      (1 - eps) *
          PFunPDE.deterministicTranscriptLaw I
            (fixedQueryDDE (Y := Y) xs) q t ≤
        PFunPDE.deterministicTranscriptLaw R
          (fixedQueryDDE (Y := Y) xs) q t)
    (t : PFunPDE.TranscriptPrefix X Y q) :
    (1 - eps) * PFunPDS.Prob.transcriptLaw I E q t ≤
      PFunPDS.Prob.transcriptLaw R E q t := by
  rcases t with ⟨xv, yv⟩
  let xs : Fin q → X := functionOfVector xv
  have h_sys :
      (1 - eps) *
          PFunPDE.transcriptSystemFactor I
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            xv yv ≤
        PFunPDE.transcriptSystemFactor R
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y)
          xv yv := by
    have hI :
        PFunPDE.deterministicTranscriptLaw I
            (fixedQueryDDE (Y := Y) xs) q (xv, yv) =
          PFunPDE.transcriptSystemFactor I
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            xv yv := by
      simpa [PFunPDE.deterministicTranscriptLaw, fixedQueryEnvironment, xs] using
        transcriptLaw_fixedQueryEnvironment_of_eq I
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y)
          xs yv
    have hR :
        PFunPDE.deterministicTranscriptLaw R
            (fixedQueryDDE (Y := Y) xs) q (xv, yv) =
          PFunPDE.transcriptSystemFactor R
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            xv yv := by
      simpa [PFunPDE.deterministicTranscriptLaw, fixedQueryEnvironment, xs] using
        transcriptLaw_fixedQueryEnvironment_of_eq R
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y)
          xs yv
    have h := h_fixed xs (xv, yv)
    rw [hI, hR] at h
    exact h
  change (1 - eps) *
        PFunPDE.transcriptLaw I E
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y)
          ((fun e : PFunDDS.DDE X Y => e) :
            PFunPDE.RV (PFunDDS.DDE X Y) X Y)
          q (xv, yv) ≤
      PFunPDE.transcriptLaw R E
        ((fun s : PFunDDS.DDS X Y => s) :
          PFunPDS.RV (PFunDDS.DDS X Y) X Y)
        ((fun e : PFunDDS.DDE X Y => e) :
          PFunPDE.RV (PFunDDS.DDE X Y) X Y)
        q (xv, yv)
  cr18_transcript
  calc (1 - eps) *
        (PFunPDE.transcriptSystemFactor I
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            xv yv *
          PFunPDE.transcriptEnvironmentFactor E
            ((fun e : PFunDDS.DDE X Y => e) :
              PFunPDE.RV (PFunDDS.DDE X Y) X Y)
            xv yv)
      = ((1 - eps) *
          PFunPDE.transcriptSystemFactor I
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            xv yv) *
          PFunPDE.transcriptEnvironmentFactor E
            ((fun e : PFunDDS.DDE X Y => e) :
              PFunPDE.RV (PFunDDS.DDE X Y) X Y)
            xv yv := by rw [← mul_assoc]
    _ ≤ PFunPDE.transcriptSystemFactor R
          ((fun s : PFunDDS.DDS X Y => s) :
            PFunPDS.RV (PFunDDS.DDS X Y) X Y)
          xv yv *
        PFunPDE.transcriptEnvironmentFactor E
          ((fun e : PFunDDS.DDE X Y => e) :
            PFunPDE.RV (PFunDDS.DDE X Y) X Y)
          xv yv := by
        gcongr

/-- Law-level fixed-query pointwise transcript-law ratios give the one-sided
H-technique bound for every law-level CR18 environment. -/
theorem oneSided_hTechnique_law_experiment_of_fixedQuery_ratio
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (R I : PFunPDS.Prob X Y)
    (E : PFunPDE.Prob X Y)
    (eps : NNReal)
    (hRtotal : R.KStepTotal q)
    (hItotal : I.KStepTotal q)
    (hEtotal : E.KQueryTotal q)
    (h_fixed : ∀ (xs : Fin q → X) (t : PFunPDE.TranscriptPrefix X Y q),
      (1 - eps) *
          PFunPDE.deterministicTranscriptLaw I
            (fixedQueryDDE (Y := Y) xs) q t ≤
        PFunPDE.deterministicTranscriptLaw R
          (fixedQueryDDE (Y := Y) xs) q t) :
    RandomSystems.statDist
        (PFunPDS.Prob.transcriptDist (q := q) R E)
        (PFunPDS.Prob.transcriptDist (q := q) I E) ≤ eps := by
  have h_weight :
      (PFunPDS.Prob.transcriptDist (q := q) R E).weight =
      (PFunPDS.Prob.transcriptDist (q := q) I E).weight := by
    have hR := PFunPDS.Prob.transcriptDist_weight_eq_one_of_total
      (q := q) R E hRtotal hEtotal
    have hI := PFunPDS.Prob.transcriptDist_weight_eq_one_of_total
      (q := q) I E hItotal hEtotal
    exact hR.trans hI.symm
  refine RandomSystems.statDist_le_of_one_sub_mul_le
    (PFunPDS.Prob.transcriptDist (q := q) R E)
    (PFunPDS.Prob.transcriptDist (q := q) I E)
    eps h_weight
    (PFunPDS.Prob.transcriptDist_weight_le_one (q := q) I E)
    ?_
  intro t
  simpa [PFunPDS.Prob.transcriptDist, PFunPDE.transcriptLawDist_apply] using
    transcriptLaw_ratio_of_fixedQuery_ratio_law R I E eps h_fixed t

end CR18
end RandomSystems
