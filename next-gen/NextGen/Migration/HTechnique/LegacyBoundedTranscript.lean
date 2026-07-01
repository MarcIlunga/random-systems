/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.AdaptiveTranscriptAdvantage
import NextGen.FixedQuery
import RandomSystems.Advantage
import RandomSystems.PDS

/-!
# Legacy bounded transcript bridge

This module is the explicit reconciliation boundary between the old bounded
`DDS`/`DDE`/`PDS.adaptiveTranscriptDist` API and the CR18 `PFun` transcript-law
surface used by the H-technique migration.

Source status:

* source-theorem bridge; candidate for upstream: a bounded old-style
  `DDS X Y q` embeds as a CR18 partial DDS whose domain is exactly the
  nonempty histories of length at most `q`;
* source-theorem bridge; candidate for upstream: an old bounded transcript
  `Fin q -> X × Y` embeds as the CR18 transcript prefix `(x^q,y^q)`;
* support lemma forced by formalization: package a legacy `PDS` probability
  assumption as the sample distribution expected by `PFunPDE.transcriptLaw`.

The embedding is tight.  In particular, it does not use `default : X`, does not
extend the old bounded system past its query budget, and does not over-approximate
the queried transcript event.

Migration note: this module is a support boundary for legacy bounded-system
compatibility.  New proofs should use CR18 `PFun` law-level transcript objects
directly.
-/

noncomputable section

namespace NextGen
namespace Migration
namespace HTechnique

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **Source-theorem bridge; candidate for upstream.** Convert an old bounded
transcript into the CR18 length-indexed transcript-prefix carrier. -/
def legacyTranscriptPrefix (t : RandomSystems.Transcript X Y q) :
    TranscriptPrefix X Y q :=
  (RandomSystems.CR18.vectorOfFunction (fun i => (t i).1),
    RandomSystems.CR18.vectorOfFunction (fun i => (t i).2))

@[simp]
theorem legacyTranscriptPrefix_fst_get
    (t : RandomSystems.Transcript X Y q) (i : Fin q) :
    (legacyTranscriptPrefix t).1.get i = (t i).1 := by
  change (RandomSystems.CR18.vectorOfFunction (fun i => (t i).1)).get i = (t i).1
  rw [RandomSystems.CR18.vectorOfFunction, List.Vector.get_ofFn]

@[simp]
theorem legacyTranscriptPrefix_snd_get
    (t : RandomSystems.Transcript X Y q) (i : Fin q) :
    (legacyTranscriptPrefix t).2.get i = (t i).2 := by
  change (RandomSystems.CR18.vectorOfFunction (fun i => (t i).2)).get i = (t i).2
  rw [RandomSystems.CR18.vectorOfFunction, List.Vector.get_ofFn]

/-- **Source-theorem bridge; candidate for upstream.** The embedding from old
bounded transcripts to CR18 transcript prefixes is injective. -/
theorem legacyTranscriptPrefix_injective :
    Function.Injective (legacyTranscriptPrefix (X := X) (Y := Y) (q := q)) := by
  intro t u h
  funext i
  apply Prod.ext
  · have hi := congrArg
      (fun z : TranscriptPrefix X Y q => z.1.get i) h
    simpa using hi
  · have hi := congrArg
      (fun z : TranscriptPrefix X Y q => z.2.get i) h
    simpa using hi

@[simp]
theorem legacyTranscriptPrefix_fst_toList (t : RandomSystems.Transcript X Y q) :
    (legacyTranscriptPrefix t).1.toList = List.ofFn (fun i : Fin q => (t i).1) := by
  change (RandomSystems.CR18.vectorOfFunction (fun i => (t i).1)).toList =
    List.ofFn (fun i : Fin q => (t i).1)
  rw [RandomSystems.CR18.vectorOfFunction, List.Vector.toList_ofFn]

/-- **Support lemma forced by formalization; candidate for upstream.** The
first projection of a legacy interaction transcript is the legacy interaction
input. -/
@[simp]
theorem legacyInteract_fst
    (s : RandomSystems.DDS X Y q) (e : RandomSystems.DDE X Y q) (i : Fin q) :
    (RandomSystems.interact s e i).1 = RandomSystems.interactInput s e i := by
  rfl

/-- **Support lemma forced by formalization; candidate for upstream.** The
second projection of a legacy interaction transcript is the legacy system
response on the interaction input prefix. -/
@[simp]
theorem legacyInteract_snd
    (s : RandomSystems.DDS X Y q) (e : RandomSystems.DDE X Y q) (i : Fin q) :
    (RandomSystems.interact s e i).2 =
      s.respond i (fun j =>
        RandomSystems.interactInput s e
          ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩) := by
  rfl

/-- **Source-theorem bridge; candidate for upstream.** Embed a bounded old-style
deterministic system as a CR18 partial DDS.

The domain is exactly the old bounded domain: nonempty input histories of length
at most `q`.  For a history of length `i + 1`, the output is the legacy
`respond i` applied to that complete input prefix. -/
def legacyBoundedDDS (s : RandomSystems.DDS X Y q) :
    RandomSystems.CR18.PFunDDS.DDS X Y :=
  ⟨(fun xs : List X =>
      (⟨xs ≠ [] ∧ xs.length ≤ q,
        fun h =>
          let n := xs.length - 1
          have hpos : 0 < xs.length := by
            cases xs with
            | nil => exact False.elim (h.1 rfl)
            | cons _ _ => simp
          have hnq : n < q := by
            dsimp [n]
            omega
          s.respond ⟨n, hnq⟩ (fun j => xs.get ⟨j.1, by
            have hj : j.1 < n + 1 := j.2
            dsimp [n] at hj
            have hpos : 0 < xs.length := by
              cases xs with
              | nil => exact False.elim (h.1 rfl)
              | cons _ _ => simp
            omega⟩)⟩ : Part Y)),
    ⟨by
      intro h
      exact h.1 rfl,
    by
      intro l₁ l₂ hprefix hne hdom
      exact ⟨hne, Nat.le_trans hprefix.length_le hdom.2⟩⟩⟩

@[simp]
theorem legacyBoundedDDS_dom_iff (s : RandomSystems.DDS X Y q) (xs : List X) :
    xs ∈ RandomSystems.CR18.PFunDDS.dom (legacyBoundedDDS s) ↔
      xs ≠ [] ∧ xs.length ≤ q := by
  rfl

/-- **Support lemma forced by formalization; candidate for upstream.** Evaluating
the embedded old bounded DDS on a prefix of a length-`q` input vector is exactly
the old bounded response at that prefix length. -/
theorem legacyBoundedDDS_eval_vector_prefix
    (s : RandomSystems.DDS X Y q) (xs : Fin q → X) (i : Fin q) :
    (legacyBoundedDDS s).1 (List.take (i.1 + 1) (List.ofFn xs)) =
      Part.some (s.respond i (fun j =>
        xs ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩)) := by
  let L := List.take (i.1 + 1) (List.ofFn xs)
  have hlen : L.length = i.1 + 1 := by
    dsimp [L]
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.succ_le_of_lt i.2)]
  have hdom : ((legacyBoundedDDS s).1 L).Dom := by
    dsimp [legacyBoundedDDS]
    constructor
    · intro hnil
      have : L.length = 0 := by simp [hnil]
      omega
    · rw [hlen]
      exact Nat.succ_le_of_lt i.2
  rw [← Part.some_get hdom]
  subst L
  congr 1
  simp [legacyBoundedDDS, List.get_eq_getElem]
  apply RandomSystems.DDS.respond_congr_val s
  · omega
  · intro k hki hkj
    rfl

/-- **Source-theorem bridge; candidate for upstream.** The random-variable view
of `legacyBoundedDDS`: sample an old bounded DDS, then regard it as a CR18
partial DDS. -/
def legacyBoundedDDSRV :
    RandomSystems.CR18.PFunPDS.RV (RandomSystems.DDS X Y q) X Y :=
  legacyBoundedDDS

/-- **Source-theorem bridge; candidate for upstream.** The embedded old bounded
DDS random variable is total on every nonempty input history up to the legacy
query budget `q`. -/
theorem legacyBoundedDDSRV_KStepTotal :
    RandomSystems.CR18.PFunPDS.RV.KStepTotal
      (legacyBoundedDDSRV (X := X) (Y := Y) (q := q)) q := by
  intro s xs hne hlen
  have hdom : xs ∈ RandomSystems.CR18.PFunDDS.dom (legacyBoundedDDS s) := by
    exact ⟨hne, hlen⟩
  refine ⟨RandomSystems.CR18.PFunDDS.output (legacyBoundedDDS s) xs hdom, ?_⟩
  exact (Part.some_get hdom).symm

/-- **Source-theorem bridge; candidate for upstream.** The CR18 environment
rectangle event for the bounded embedding of a legacy environment is exactly
the environment side of the legacy interaction transcript. -/
theorem transcriptEnvironmentEvent_boundedEnvironment_legacyTranscriptPrefix_interact
    (s : RandomSystems.DDS X Y q) (e : RandomSystems.DDE X Y q) :
    RandomSystems.CR18.PFunPDE.transcriptEnvironmentEvent
      (boundedEnvironment e.choose)
      (legacyTranscriptPrefix (RandomSystems.interact s e)).1
      (legacyTranscriptPrefix (RandomSystems.interact s e)).2
      PUnit.unit := by
  intro i hi
  have htoList : (legacyTranscriptPrefix (RandomSystems.interact s e)).2.toList =
      List.ofFn (fun j : Fin q => (RandomSystems.interact s e j).2) := by
    change (RandomSystems.CR18.vectorOfFunction
      (fun j : Fin q => (RandomSystems.interact s e j).2)).toList =
        List.ofFn (fun j : Fin q => (RandomSystems.interact s e j).2)
    rw [RandomSystems.CR18.vectorOfFunction, List.Vector.toList_ofFn]
  rw [htoList]
  let ys := List.take i (List.ofFn fun j : Fin q => (RandomSystems.interact s e j).2)
  have hlen_eq : ys.length = i := by
    dsimp [ys]
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt hi)]
  change boundedDDE e.choose (ys.map some) =
    some ((legacyTranscriptPrefix (RandomSystems.interact s e)).1.get ⟨i, hi⟩)
  rw [boundedDDE_apply_map_some_of_length_eq e.choose ys ⟨i, hi⟩ hlen_eq]
  rw [legacyTranscriptPrefix_fst_get]
  rw [legacyInteract_fst]
  unfold RandomSystems.interactInput
  congr
  funext j
  simp [ys, List.get_eq_getElem]

/-- **Source-theorem bridge; candidate for upstream.** The CR18 system
rectangle event for the bounded embedding of a legacy system is exactly the
system side of the legacy interaction transcript. -/
theorem transcriptSystemEvent_legacyBoundedDDSRV_legacyTranscriptPrefix_interact
    (s : RandomSystems.DDS X Y q) (e : RandomSystems.DDE X Y q) :
    RandomSystems.CR18.PFunPDE.transcriptSystemEvent
      (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
      (legacyTranscriptPrefix (RandomSystems.interact s e)).1
      (legacyTranscriptPrefix (RandomSystems.interact s e)).2
      s := by
  intro i hi
  rw [legacyTranscriptPrefix_snd_get]
  rw [legacyInteract_snd]
  rw [legacyTranscriptPrefix_fst_toList]
  simpa [RandomSystems.CR18.PFunPDS.funView, legacyBoundedDDSRV,
    RandomSystems.Dist.RV.eval, legacyInteract_fst] using
      legacyBoundedDDS_eval_vector_prefix
        (s := s) (xs := fun j : Fin q => RandomSystems.interactInput s e j) ⟨i, hi⟩

/-- **Source-theorem bridge; candidate for upstream.** For a fixed legacy
bounded system/environment sample, the CR18 joint transcript event for the
embedded system and bounded environment is exactly equality with the embedded
legacy interaction transcript.

This is the tight event bridge: no default query, no extension past the old
query budget, and no over-approximation of the queried transcript event. -/
theorem transcriptJointEvent_legacyBoundedDDSRV_boundedEnvironment_iff
    (s : RandomSystems.DDS X Y q) (e : RandomSystems.DDE X Y q)
    (t : TranscriptPrefix X Y q) :
    RandomSystems.CR18.PFunPDE.transcriptJointEvent
      (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
      (boundedEnvironment e.choose) t (s, PUnit.unit) ↔
      legacyTranscriptPrefix (RandomSystems.interact s e) = t := by
  constructor
  · intro h
    exact (RandomSystems.CR18.PFunPDE.transcriptJointEvent_unique
      (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
      (boundedEnvironment e.choose) t
      (legacyTranscriptPrefix (RandomSystems.interact s e)) (s, PUnit.unit) h
      ⟨transcriptSystemEvent_legacyBoundedDDSRV_legacyTranscriptPrefix_interact s e,
       transcriptEnvironmentEvent_boundedEnvironment_legacyTranscriptPrefix_interact s e⟩).symm
  · intro ht
    rw [← ht]
    exact ⟨transcriptSystemEvent_legacyBoundedDDSRV_legacyTranscriptPrefix_interact s e,
       transcriptEnvironmentEvent_boundedEnvironment_legacyTranscriptPrefix_interact s e⟩

/-- **Support lemma forced by formalization.** Package the probability
assumption on a legacy `PDS` as the sample distribution required by CR18
transcript laws. -/
def legacyPDSProbDist [Fintype (RandomSystems.DDS X Y q)]
    (S : RandomSystems.PDS X Y q) (hS : S.dist.isProbDist) :
    RandomSystems.Dist.ProbDist (RandomSystems.DDS X Y q) :=
  ⟨S.dist, hS⟩

/-- **Source-theorem bridge; candidate for upstream.** Package an old bounded
`PDS` as the CR18 representative used by the transcript-law migration layer.

This is only a boundary adapter: the public legacy endpoint still takes the old
high-level `PDS`, while the constructed representative hides the sample space,
probability distribution, and embedded partial-system RV. -/
def legacyPDSRepresentative [Fintype (RandomSystems.DDS X Y q)]
    (S : RandomSystems.PDS X Y q) (hS : S.dist.isProbDist) :
    PDSRepresentative X Y where
  Ω := RandomSystems.DDS X Y q
  prob := legacyPDSProbDist S hS
  rv := legacyBoundedDDSRV (X := X) (Y := Y) (q := q)

/-- **Source-theorem bridge; candidate for upstream.** The old bounded adaptive
transcript distribution, pushed through the exact CR18 transcript-prefix
embedding, is the CR18 transcript-law distribution of the embedded legacy
system and bounded environment.

This is the distribution-level reconciliation theorem between the old bounded
`PDS.adaptiveTranscriptDist` API and the CR18 `PFunPDE.transcriptLawDist` API. -/
theorem legacyTranscriptPrefix_adaptiveTranscriptDist_eq_transcriptLawDist
    [Fintype (RandomSystems.DDS X Y q)]
    [Fintype (RandomSystems.Transcript X Y q)]
    [DecidableEq (RandomSystems.Transcript X Y q)]
    [FiniteTranscriptSpace X Y q]
    (S : RandomSystems.PDS X Y q) (hS : S.dist.isProbDist)
    (e : RandomSystems.DDE X Y q) :
    RandomSystems.Dist.fTransform legacyTranscriptPrefix (S.adaptiveTranscriptDist e) =
      RandomSystems.CR18.PFunPDE.transcriptLawDist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (legacyPDSProbDist S hS) RandomSystems.Dist.unitProbDist
          (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
          (boundedEnvironment e.choose) q) := by
  ext t
  rw [RandomSystems.Dist.fTransform_apply_eq_mass]
  rw [RandomSystems.CR18.PFunPDE.transcriptLawDist_apply,
    RandomSystems.CR18.PFunPDE.transcriptLaw_apply,
    RandomSystems.CR18.PFunPDE.transcriptDist_eq_mass_jointEvent]
  rw [RandomSystems.Dist.prodProbDist_val]
  rw [RandomSystems.Dist.mass_prod_unitProbDist_right]
  unfold RandomSystems.PDS.adaptiveTranscriptDist
  rw [RandomSystems.Dist.mass_fTransform]
  simp [legacyPDSProbDist]
  apply RandomSystems.Dist.mass_congr
  intro s
  exact (transcriptJointEvent_legacyBoundedDDSRV_boundedEnvironment_iff s e t).symm

/-- **Source-theorem bridge; candidate for upstream.** For each old bounded
deterministic environment, statistical distance between old adaptive transcript
laws is exactly the statistical distance between the corresponding CR18
transcript-law distributions for the embedded systems and bounded environment. -/
theorem statDist_adaptiveTranscriptDist_eq_transcriptLawDist_boundedEnvironment
    [Fintype (RandomSystems.DDS X Y q)]
    [Fintype (RandomSystems.Transcript X Y q)]
    [DecidableEq (RandomSystems.Transcript X Y q)]
    [FiniteTranscriptSpace X Y q]
    [DiscreteTranscriptSpace X Y q]
    (S T : RandomSystems.PDS X Y q)
    (hS : S.dist.isProbDist) (hT : T.dist.isProbDist)
    (e : RandomSystems.DDE X Y q) :
    RandomSystems.statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) =
      RandomSystems.statDist
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (legacyPDSProbDist S hS) RandomSystems.Dist.unitProbDist
            (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
            (boundedEnvironment e.choose) q))
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (legacyPDSProbDist T hT) RandomSystems.Dist.unitProbDist
            (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
            (boundedEnvironment e.choose) q)) := by
  rw [← RandomSystems.statDist_fTransform_injective
    (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e)
    legacyTranscriptPrefix legacyTranscriptPrefix_injective]
  rw [legacyTranscriptPrefix_adaptiveTranscriptDist_eq_transcriptLawDist S hS e,
    legacyTranscriptPrefix_adaptiveTranscriptDist_eq_transcriptLawDist T hT e]

/-- **Source-theorem bridge; candidate for upstream.** The CR18 bounded
transcript-law advantage associated with two old bounded `PDS` representatives,
constructed through the exact legacy embedding.

This is the named endpoint for the long constructed RHS used by
`advantageAdaptive_le_boundedAdaptiveTranscriptAdvantage`. -/
noncomputable abbrev legacyBoundedAdaptiveTranscriptAdvantage
    [Fintype (RandomSystems.DDS X Y q)]
    [FiniteTranscriptSpace X Y q]
    (S T : RandomSystems.PDS X Y q)
    (hS : S.dist.isProbDist) (hT : T.dist.isProbDist) : ℝ :=
  boundedAdaptiveTranscriptAdvantage
    (q := q)
    (legacyPDSRepresentative S hS)
    (legacyPDSRepresentative T hT)

/-- **Source-theorem bridge; candidate for upstream.** The old bounded adaptive
advantage is bounded by the migrated CR18 bounded-environment transcript
supremum for the exact legacy embedding. -/
theorem advantageAdaptive_le_boundedAdaptiveTranscriptAdvantage
    [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype (RandomSystems.DDS X Y q)]
    [Fintype (RandomSystems.Transcript X Y q)]
    [DecidableEq (RandomSystems.Transcript X Y q)]
    [FiniteTranscriptSpace X Y q]
    [DiscreteTranscriptSpace X Y q]
    (S T : RandomSystems.PDS X Y q)
    (hS : S.dist.isProbDist) (hT : T.dist.isProbDist) :
    (RandomSystems.advantageAdaptive S T : ℝ) ≤
      legacyBoundedAdaptiveTranscriptAdvantage S T hS hT := by
  unfold RandomSystems.advantageAdaptive
  refine RandomSystems.coe_finset_sup_le
    (Finset.univ : Finset (RandomSystems.DDE X Y q))
    (fun e => RandomSystems.statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e))
    (boundedAdaptiveTranscriptAdvantage_nonneg
      (q := q)
      (legacyPDSRepresentative S hS)
      (legacyPDSRepresentative T hT)) ?_
  intro e _he
  change (((RandomSystems.statDist (S.adaptiveTranscriptDist e)
      (T.adaptiveTranscriptDist e) : NNReal) : ℝ) ≤
    boundedAdaptiveTranscriptAdvantage
      (q := q)
      (legacyPDSRepresentative S hS)
      (legacyPDSRepresentative T hT))
  rw [statDist_adaptiveTranscriptDist_eq_transcriptLawDist_boundedEnvironment S T hS hT e]
  have hSdet :
      ProbPDS.deterministicTranscriptDist (q := q)
          (RandomSystems.Dist.PMF (legacyPDSRepresentative S hS).prob
            (legacyPDSRepresentative S hS).rv)
          (RandomSystems.CR18.boundedDDE e.choose) =
        TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (legacyPDSProbDist S hS) RandomSystems.Dist.unitProbDist
            (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
            (RandomSystems.CR18.boundedEnvironment e.choose) q) := by
    calc
      ProbPDS.deterministicTranscriptDist (q := q)
          (RandomSystems.Dist.PMF (legacyPDSRepresentative S hS).prob
            (legacyPDSRepresentative S hS).rv)
          (RandomSystems.CR18.boundedDDE e.choose)
          = PDSRepresentative.transcriptDist (q := q) (legacyPDSRepresentative S hS)
              (PDERepresentative.ofDDE (RandomSystems.CR18.boundedDDE e.choose)) := by
              exact PDSRepresentative.deterministicTranscriptDist_ofProbPDS_pmf
                (q := q)
                (legacyPDSRepresentative S hS)
                (RandomSystems.CR18.boundedDDE e.choose)
      _ = TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (legacyPDSProbDist S hS) RandomSystems.Dist.unitProbDist
            (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
            (RandomSystems.CR18.boundedEnvironment e.choose) q) := by
              unfold RandomSystems.CR18.boundedEnvironment
              simp [TranscriptLawBridge.dist, PDSRepresentative.transcriptDist,
                PDSRepresentative.transcriptLaw, PDERepresentative.ofDDE,
                PDERepresentative.deterministic, legacyPDSRepresentative]
              rfl
  have hTdet :
      ProbPDS.deterministicTranscriptDist (q := q)
          (RandomSystems.Dist.PMF (legacyPDSRepresentative T hT).prob
            (legacyPDSRepresentative T hT).rv)
          (RandomSystems.CR18.boundedDDE e.choose) =
        TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (legacyPDSProbDist T hT) RandomSystems.Dist.unitProbDist
            (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
            (RandomSystems.CR18.boundedEnvironment e.choose) q) := by
    calc
      ProbPDS.deterministicTranscriptDist (q := q)
          (RandomSystems.Dist.PMF (legacyPDSRepresentative T hT).prob
            (legacyPDSRepresentative T hT).rv)
          (RandomSystems.CR18.boundedDDE e.choose)
          = PDSRepresentative.transcriptDist (q := q) (legacyPDSRepresentative T hT)
              (PDERepresentative.ofDDE (RandomSystems.CR18.boundedDDE e.choose)) := by
              exact PDSRepresentative.deterministicTranscriptDist_ofProbPDS_pmf
                (q := q)
                (legacyPDSRepresentative T hT)
                (RandomSystems.CR18.boundedDDE e.choose)
      _ = TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (legacyPDSProbDist T hT) RandomSystems.Dist.unitProbDist
            (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
            (RandomSystems.CR18.boundedEnvironment e.choose) q) := by
              unfold RandomSystems.CR18.boundedEnvironment
              simp [TranscriptLawBridge.dist, PDSRepresentative.transcriptDist,
                PDSRepresentative.transcriptLaw, PDERepresentative.ofDDE,
                PDERepresentative.deterministic, legacyPDSRepresentative]
              rfl
  exact le_csSup
    (boundedAdaptiveTranscriptLawAdvantage_image_bddAbove
      (q := q)
      (RandomSystems.Dist.PMF (legacyPDSRepresentative S hS).prob
        (legacyPDSRepresentative S hS).rv)
      (RandomSystems.Dist.PMF (legacyPDSRepresentative T hT).prob
        (legacyPDSRepresentative T hT).rv))
    ⟨e.choose, Set.mem_univ _, by
      change ((RandomSystems.statDist
          (ProbPDS.deterministicTranscriptDist (q := q)
            (RandomSystems.Dist.PMF (legacyPDSRepresentative S hS).prob
              (legacyPDSRepresentative S hS).rv)
            (RandomSystems.CR18.boundedDDE e.choose))
          (ProbPDS.deterministicTranscriptDist (q := q)
            (RandomSystems.Dist.PMF (legacyPDSRepresentative T hT).prob
              (legacyPDSRepresentative T hT).rv)
            (RandomSystems.CR18.boundedDDE e.choose)) : NNReal) : ℝ) =
        ((RandomSystems.statDist
          (TranscriptLawBridge.dist
            (RandomSystems.CR18.PFunPDE.transcriptLaw
              (legacyPDSProbDist S hS) RandomSystems.Dist.unitProbDist
              (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
              (boundedEnvironment e.choose) q))
          (TranscriptLawBridge.dist
            (RandomSystems.CR18.PFunPDE.transcriptLaw
              (legacyPDSProbDist T hT) RandomSystems.Dist.unitProbDist
              (legacyBoundedDDSRV (X := X) (Y := Y) (q := q))
              (boundedEnvironment e.choose) q)) : NNReal) : ℝ)
      rw [hSdet, hTdet]⟩

/-- **Source-theorem bridge; candidate for upstream.** If the migrated CR18
bounded transcript-law endpoint for old bounded representatives is bounded by a
concrete `NNReal` error term, then the old finite `advantageAdaptive` endpoint
has the same `NNReal` bound. -/
theorem advantageAdaptive_le_of_legacyBoundedAdaptiveTranscriptAdvantage_le
    [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype (RandomSystems.DDS X Y q)]
    [Fintype (RandomSystems.Transcript X Y q)]
    [DecidableEq (RandomSystems.Transcript X Y q)]
    [FiniteTranscriptSpace X Y q]
    [DiscreteTranscriptSpace X Y q]
    (S T : RandomSystems.PDS X Y q)
    (hS : S.dist.isProbDist) (hT : T.dist.isProbDist)
    (eps : NNReal)
    (hbound : legacyBoundedAdaptiveTranscriptAdvantage S T hS hT ≤ (eps : ℝ)) :
    RandomSystems.advantageAdaptive S T ≤ eps := by
  exact NNReal.coe_le_coe.mp (le_trans
    (advantageAdaptive_le_boundedAdaptiveTranscriptAdvantage S T hS hT) hbound)

end HTechnique
end Migration
end NextGen
