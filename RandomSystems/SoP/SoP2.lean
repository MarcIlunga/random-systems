/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.Common
import RandomSystems.Legacy.Applications.XoPAnalytic

/-!
# SoP2: sum of two independent permutations

This file formalizes the coupling proof developed in
`RandomSystems/SoP/SoP2.md`.
The public objects are law-level CR18 probabilistic deterministic systems.

The declarations follow the proof dependency graph:

1. define the two concrete law-level systems;
2. instantiate the shared honest tape-representative infrastructure;
3. construct and audit the exact maximal coupling;
4. check small-query and saturation boundary cases;
5. derive the direct sequential cubic benchmark;
6. analyze the optimal coupling at finite parameters; and
7. state the strongest public law-level distinguishing bound last.

Internal tape, fiber, and analytic objects are introduced only where the next
proof obligation requires them.  In particular, no implementation object
occurs in the final security theorem.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18

namespace RandomSystems.SoP

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open Common

variable (G : Type*) [Fintype G] [AddGroup G]

section TwoPermutationSum

/-!
## 1. Concrete models

The construction begins with the literal pointwise sum of two independent
uniform permutations and the uniform random-function ideal.  The fresh-tape
laws are the finite observations later coupled.
-/

/-- The literal pointwise sum of two permutations. -/
def xop_function (p : Equiv.Perm G × Equiv.Perm G) : G → G :=
  fun x => p.1 x + p.2 x

/-- The real law-level oracle: the pointwise sum of two independent uniform
permutations. -/
noncomputable def xop : PFunPDS.Prob G G :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform (Equiv.Perm G × Equiv.Perm G), Dist.uniform_isProbDist⟩
    (xop_function G)

/-- The ideal law-level oracle: a uniform random function from `G` to `G`. -/
noncomputable def urf : PFunPDS.Prob G G :=
  PFunPDS.Prob.urf (X := G) (Y := G)

/-- The real fresh-output tape on a fixed injective query schedule. -/
noncomputable def real_fresh_tape {q : Nat} (xs : Fin q ↪ G) :
    Dist.ProbDist (Fin q → G) :=
  ⟨Dist.fTransform
      (fun p : Equiv.Perm G × Equiv.Perm G =>
        fun i => xop_function G p (xs i))
      (Dist.uniform (Equiv.Perm G × Equiv.Perm G)),
    Dist.fTransform_isProbDist
      (fun p : Equiv.Perm G × Equiv.Perm G =>
        fun i => xop_function G p (xs i))
      Dist.uniform_isProbDist⟩

/-- The ideal fresh-output tape. -/
noncomputable def ideal_fresh_tape (q : Nat) : Dist.ProbDist (Fin q → G) :=
  ⟨Dist.uniform (Fin q → G), Dist.uniform_isProbDist⟩

/-!
### Literal sum versus difference normalization

The concrete legacy counting theory uses `-π₁(x) + π₂(x)`, whereas the public
oracle in this file is the literal sum `π₁(x) + π₂(x)`.  Postcomposing the
first permutation with negation is an involutive equivalence of permutation
pairs.  It preserves the uniform law and transports the normalized output
exactly to the literal sum.  Thus no change of public model is hidden in later
uses of the legacy visible-tape theorem.
-/

/-- Postcomposition with group negation is an involution on permutations. -/
private def post_neg_perm : Equiv.Perm G ≃ Equiv.Perm G where
  toFun π := π.trans (Equiv.neg G)
  invFun π := π.trans (Equiv.neg G)
  left_inv π := by ext x; simp
  right_inv π := by ext x; simp

/-- Negate the output of the first permutation and leave the second fixed. -/
private def negate_first_perm_pair :
    (Equiv.Perm G × Equiv.Perm G) ≃
      (Equiv.Perm G × Equiv.Perm G) :=
  (post_neg_perm G).prodCongr (Equiv.refl _)

/-- On every fixed input vector, the literal-sum output law is the normalized
legacy XoP output law. -/
private theorem sum_output_law_eq_legacy_normalized {q : Nat}
    (inputs : Fin q → G) :
    Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          fun i => xop_function G p (inputs i))
        (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) =
      Dist.fTransform
        (RandomSystems.Applications.XoP.Model.outputMap inputs)
        (RandomSystems.Applications.XoP.Model.xopRealPDS
          (G := G) (q := q)).dist := by
  -- First expose the legacy experiment as a pushforward of a uniform
  -- permutation pair.
  rw [RandomSystems.Applications.XoP.Model.xopReal_outputDist_eq_pair_pushforward]
  calc
    Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          fun i => xop_function G p (inputs i))
        (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) =
      Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          RandomSystems.Applications.XoP.Model.outputMap inputs
            (RandomSystems.Applications.XoP.Model.xopDDS
              (q := q) p.1 p.2))
        (Dist.fTransform (negate_first_perm_pair G)
          (Dist.uniform (Equiv.Perm G × Equiv.Perm G))) := by
            -- Pointwise, normalized difference after negating the first
            -- permutation is the literal sum.
            rw [Dist.fTransform_comp]
            congr 1
            funext p i
            simp [xop_function, negate_first_perm_pair, post_neg_perm,
              RandomSystems.Applications.XoP.Model.outputMap_xopDDS]
    -- The change of permutation coordinates preserves the uniform law.
    _ = _ := by rw [Dist.fTransform_equiv_uniform]

/-- The literal-sum fresh tape is exactly the already-proved visible-tape law
used by the legacy position-tape representative. -/
private theorem real_fresh_tape_eq_legacy_real_visible {q : Nat}
    (xs : Fin q ↪ G) (hq : q ≤ Fintype.card G) :
    (real_fresh_tape G xs).val =
      RandomSystems.Applications.SoP.realVisibleDist
        (G := G) (q := q) := by
  change
    Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          fun i => xop_function G p (xs i))
        (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) = _
  rw [sum_output_law_eq_legacy_normalized G xs]
  exact
    RandomSystems.Applications.XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
      xs xs.injective hq

/-!
## 2. Shared representative infrastructure instantiated for SoP2

### The lazy representative

The next definitions are introduced by the adaptive upper-bound obligation.
We first give, locally and explicitly, the exact bridge from the repository's
bounded deterministic systems to the CR18 partial-function carrier.  We then
apply it to the proved position-tape deterministic system: a tape coordinate
is attached to an absolute query position, and a repeated input returns the
coordinate at its first occurrence.  The resulting domain is exactly the
nonempty histories of length at most `q`.
-/

private def bounded_dds_of_legacy {q : Nat} (s : RandomSystems.DDS G G q) :
    PFunDDS.DDS G G :=
  ⟨(fun l : List G =>
      (⟨l ≠ [] ∧ l.length ≤ q, fun h =>
        let n := l.length - 1
        have hpos : 0 < l.length := by
          cases l with
          | nil => exact False.elim (h.1 rfl)
          | cons _ _ => simp
        have hnq : n < q := by
          dsimp [n]
          omega
        s.respond ⟨n, hnq⟩ (fun j => l.get ⟨j.1, by
          have hj : j.1 < n + 1 := j.2
          dsimp [n] at hj
          omega⟩)⟩ : Part G)),
    ⟨by
      intro h
      exact h.1 rfl,
    by
      intro l₁ l₂ hprefix hne hdom
      exact ⟨hne, Nat.le_trans hprefix.length_le hdom.2⟩⟩⟩

/-- The local PFun representative of a position-indexed output tape. -/
private def position_tape_dds (q : Nat) (tape : Fin q → G) :
    PFunDDS.DDS G G :=
  bounded_dds_of_legacy G
    (RandomSystems.DDS.ofPositionTape (q := q) (X := G) tape)

/-- Evaluating the embedded bounded system on the prefix ending at `i`
recovers exactly the legacy response at position `i`.  This is the only
pointwise bridge needed between the two deterministic-system carriers. -/
private theorem bounded_dds_of_legacy_eval_vector_prefix
    {q : Nat} (s : RandomSystems.DDS G G q) (xs : Fin q → G) (i : Fin q) :
    (bounded_dds_of_legacy G s).1
        (List.take (i.1 + 1) (List.ofFn xs)) =
      Part.some (s.respond i (fun j =>
        xs ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩)) := by
  let L := List.take (i.1 + 1) (List.ofFn xs)
  have hlen : L.length = i.1 + 1 := by
    dsimp [L]
    rw [List.length_take, List.length_ofFn,
      Nat.min_eq_left (Nat.succ_le_of_lt i.2)]
  have hdom : ((bounded_dds_of_legacy G s).1 L).Dom := by
    dsimp [bounded_dds_of_legacy]
    constructor
    · intro hnil
      have : L.length = 0 := by simp [hnil]
      omega
    · rw [hlen]
      exact Nat.succ_le_of_lt i.2
  rw [← Part.some_get hdom]
  subst L
  congr 1
  simp [bounded_dds_of_legacy, List.get_eq_getElem]
  apply RandomSystems.DDS.respond_congr_val s
  · omega
  · intro k hki hkj
    rfl

/-- Sampling a position tape and then its deterministic lazy system. -/
private noncomputable def position_tape_prob {q : Nat}
    (D : Dist.ProbDist (Fin q → G)) : PFunPDS.Prob G G :=
  Dist.PMF D (position_tape_dds G q)

/-- Every sampled position-tape system answers every nonempty history up to
its advertised query bound. -/
private theorem position_tape_dds_k_step_total (q : Nat) :
    PFunPDS.RV.KStepTotal (position_tape_dds G q) q := by
  intro tape l hne hlen
  have hdom :
      l ∈ PFunDDS.dom (position_tape_dds G q tape) := ⟨hne, hlen⟩
  exact
    ⟨PFunDDS.output (position_tape_dds G q tape) l hdom,
      (Part.some_get hdom).symm⟩

/-!
### Shared tape representative

The application-specific work stops at the deterministic lazy system and its
totality proof.  Replay, maximal coupling, data processing, and the fixed-query
lower bound are supplied by the shared `TapeRepresentative` infrastructure.
-/

private def position_tape_representative (q : Nat) :
    Common.TapeRepresentative G G q where
  to_dds := position_tape_dds G q
  k_step_total := position_tape_dds_k_step_total G q

/-!
### Marginal transport

The adaptive theorem needs equality of honest CR18 marginals, not merely a
fixed-schedule coincidence.  We establish it through the system rectangle in
CR18 Lemma 3.2.  For every possible input and output vector, the concrete
function-evaluator factor is identified with the corresponding legacy
nonadaptive transcript mass; the same is done for the lazy position-tape
factor.  The legacy all-input representative theorem then equates those two
factors.  Since the environment factor is literally common, this yields
equality against every adaptive environment.
-/

/-- The CR18 system event for an embedded position tape is exactly the legacy
fixed-input transcript event for the same tape. -/
private theorem transcript_system_event_position_tape_iff_legacy_transcript
    {q : Nat} (tape inputs outputs : Fin q → G) :
    PFunPDE.transcriptSystemEvent
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G)
        (vectorOfFunction inputs) (vectorOfFunction outputs)
        (position_tape_dds G q tape) ↔
      RandomSystems.DDS.transcript
          (RandomSystems.DDS.ofPositionTape (q := q) (X := G) tape)
          inputs =
        RandomSystems.Transcript.ofOutputs inputs outputs := by
  constructor
  · intro h
    -- Read each CR18 prefix equation as the corresponding bounded legacy
    -- response equation, then assemble the fixed-input transcript.
    funext i
    apply Prod.ext
    · rfl
    · have hi := h i.1 i.2
      have hi' :
        (position_tape_dds G q tape).1
            (List.take (i.1 + 1) (List.ofFn inputs)) =
          Part.some (outputs i) := by
            simpa [PFunPDS.funView, Dist.RV.eval, vectorOfFunction] using hi
      rw [show position_tape_dds G q tape =
          bounded_dds_of_legacy G
            (RandomSystems.DDS.ofPositionTape (q := q) (X := G) tape) from rfl,
        bounded_dds_of_legacy_eval_vector_prefix] at hi'
      exact Part.some_inj.mp hi'
  · intro h i hi
    -- Conversely, project the legacy transcript equality at this coordinate
    -- and transport it through the exact prefix-evaluation bridge.
    have hout := congrArg Prod.snd (congr_fun h ⟨i, hi⟩)
    change
      (RandomSystems.DDS.ofPositionTape (q := q) (X := G) tape).respond
          ⟨i, hi⟩ (fun j => inputs ⟨j.1,
            Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt hi)⟩) =
        outputs ⟨i, hi⟩ at hout
    have heval :=
      bounded_dds_of_legacy_eval_vector_prefix G
        (RandomSystems.DDS.ofPositionTape (q := q) (X := G) tape)
        inputs ⟨i, hi⟩
    rw [hout] at heval
    simpa [position_tape_dds, PFunPDS.funView, Dist.RV.eval,
      vectorOfFunction] using heval

/-- The concrete legacy real system and the real visible-tape representative
have the same fixed-input transcript law for every input vector, including
vectors with repetitions. -/
private theorem legacy_real_transcript_eq_position_tape {q : Nat}
    (inputs : Fin q → G) (hq : q ≤ Fintype.card G) :
    (RandomSystems.Applications.XoP.Model.xopRealPDS
        (G := G) (q := q)).transcriptDist inputs =
      (RandomSystems.PDS.ofPositionTapeDist (q := q) (X := G)
        (RandomSystems.Applications.SoP.realVisibleDist
          (G := G) (q := q))).transcriptDist inputs := by
  -- Turn the fixed schedule into a deterministic environment on both sides.
  rw [← RandomSystems.PDS.adaptiveTranscriptDist_nonadaptive
    (S := RandomSystems.Applications.XoP.Model.xopRealPDS
      (G := G) (q := q)) (inputs := inputs)]
  rw [← RandomSystems.PDS.adaptiveTranscriptDist_nonadaptive
    (S := RandomSystems.PDS.ofPositionTapeDist (q := q) (X := G)
      (RandomSystems.Applications.SoP.realVisibleDist
        (G := G) (q := q))) (inputs := inputs)]
  -- A followed transcript is deterministic postprocessing of its output
  -- history, so it suffices to compare the two output-history laws.
  rw [RandomSystems.PDS.adaptiveTranscriptDist_eq_output_pushforward,
    RandomSystems.PDS.adaptiveTranscriptDist_eq_output_pushforward]
  -- Invoke the concrete all-input XoP marginal and identify the other side as
  -- the honest position-tape experiment.
  rw [RandomSystems.Applications.XoP.Model.xopReal_adaptiveOutputDist_eq_positionTape_realVisible
      (G := G) (q := q) (RandomSystems.DDE.nonadaptive inputs) hq]
  rw [RandomSystems.PDS.adaptiveOutputDist_ofPositionTapeDist_eq]

/-- The concrete legacy ideal system and a uniform position tape have the same
fixed-input transcript law for every input vector. -/
private theorem legacy_ideal_transcript_eq_position_tape {q : Nat}
    (inputs : Fin q → G) :
    (RandomSystems.Applications.XoP.Model.xopIdealPDS
        (G := G) (q := q)).transcriptDist inputs =
      (RandomSystems.PDS.ofPositionTapeDist (q := q) (X := G)
        (Dist.uniform (Fin q → G))).transcriptDist inputs := by
  -- The ideal proof follows the same three structural moves as the real one:
  -- nonadaptive embedding, output-history projection, and tape replay.
  rw [← RandomSystems.PDS.adaptiveTranscriptDist_nonadaptive
    (S := RandomSystems.Applications.XoP.Model.xopIdealPDS
      (G := G) (q := q)) (inputs := inputs)]
  rw [← RandomSystems.PDS.adaptiveTranscriptDist_nonadaptive
    (S := RandomSystems.PDS.ofPositionTapeDist (q := q) (X := G)
      (Dist.uniform (Fin q → G))) (inputs := inputs)]
  rw [RandomSystems.PDS.adaptiveTranscriptDist_eq_output_pushforward,
    RandomSystems.PDS.adaptiveTranscriptDist_eq_output_pushforward]
  rw [RandomSystems.Applications.XoP.Model.xopIdeal_adaptiveOutputDist_eq_positionTape_uniform
      (G := G) (q := q) (RandomSystems.DDE.nonadaptive inputs)]
  rw [RandomSystems.PDS.adaptiveOutputDist_ofPositionTapeDist_eq]

/-- The real CR18 system factor is the fixed-input output-vector mass of the
literal sum of two uniform permutations. -/
private theorem xop_system_factor_eq_output_law {q : Nat}
    (xv yv : List.Vector G q) :
    PFunPDE.transcriptSystemFactor (xop G)
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv =
      Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          fun i => xop_function G p (functionOfVector xv i))
        (Dist.uniform (Equiv.Perm G × Equiv.Perm G))
        (functionOfVector yv) := by
  unfold PFunPDE.transcriptSystemFactor xop
    PFunPDS.Prob.functionEvaluator Dist.PMF
  rw [Dist.mass_fTransform, Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr
  intro p
  change
    PFunPDE.transcriptSystemEvent
        (functionEvaluatorRV (xop_function G)) xv yv p ↔ _
  rw [transcriptSystemEvent_functionEvaluatorRV_iff]
  constructor
  · intro h
    funext i
    simpa [functionOfVector] using h i
  · intro h i
    simpa [functionOfVector] using congr_fun h i

/-- The ideal CR18 system factor is the fixed-input output-vector mass of a
uniform random function. -/
private theorem urf_system_factor_eq_output_law {q : Nat}
    (xv yv : List.Vector G q) :
    PFunPDE.transcriptSystemFactor (urf G)
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv =
      Dist.fTransform
        (fun f : G → G => fun i => f (functionOfVector xv i))
        (Dist.uniform (G → G)) (functionOfVector yv) := by
  unfold PFunPDE.transcriptSystemFactor urf
    PFunPDS.Prob.urf Dist.PMF
  rw [Dist.mass_fTransform, Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr
  intro f
  change
    PFunPDE.transcriptSystemEvent
        (functionEvaluatorRV (fun f : G → G => f)) xv yv f ↔ _
  rw [transcriptSystemEvent_functionEvaluatorRV_iff]
  constructor
  · intro h
    funext i
    simpa [functionOfVector] using h i
  · intro h i
    simpa [functionOfVector] using congr_fun h i

/-- The CR18 system factor of a sampled position tape is the corresponding
legacy position-tape transcript mass. -/
private theorem position_tape_system_factor_eq_legacy_transcript
    {q : Nat} (D : Dist.ProbDist (Fin q → G))
    (xv yv : List.Vector G q) :
    PFunPDE.transcriptSystemFactor (position_tape_prob G D)
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv =
      (RandomSystems.PDS.ofPositionTapeDist
        (q := q) (X := G) D.val).transcriptDist (functionOfVector xv)
          (RandomSystems.Transcript.ofOutputs
            (functionOfVector xv) (functionOfVector yv)) := by
  rw [← vectorOfFunction_functionOfVector xv,
    ← vectorOfFunction_functionOfVector yv]
  unfold PFunPDE.transcriptSystemFactor position_tape_prob Dist.PMF
  rw [Dist.mass_fTransform]
  unfold RandomSystems.PDS.transcriptDist
    RandomSystems.PDS.ofPositionTapeDist
  rw [Dist.fTransform_comp, Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr
  intro tape
  simpa [Function.comp_def] using
    (transcript_system_event_position_tape_iff_legacy_transcript
      G tape (functionOfVector xv) (functionOfVector yv))

/-- Evaluating a legacy fixed-input transcript law at the canonical transcript
is the corresponding output-vector mass. -/
private theorem legacy_transcript_apply_eq_output_law
    {q : Nat} (S : RandomSystems.PDS G G q)
    (inputs outputs : Fin q → G) :
    S.transcriptDist inputs
        (RandomSystems.Transcript.ofOutputs inputs outputs) =
      Dist.fTransform
        (RandomSystems.Applications.XoP.Model.outputMap inputs)
        S.dist outputs := by
  rw [RandomSystems.Applications.XoP.Model.transcriptDist_eq_output_pushforward]
  exact RandomSystems.fTransform_injective_apply _ _
    (RandomSystems.Applications.XoP.Model.transcriptEmbed_injective inputs)
    outputs

/-- The modern and legacy presentations of the ideal fixed-input output law
are definitionally the same uniform-function experiment. -/
private theorem urf_output_law_eq_legacy_ideal {q : Nat}
    (inputs : Fin q → G) :
    Dist.fTransform
        (fun f : G → G => fun i => f (inputs i))
        (Dist.uniform (G → G)) =
      Dist.fTransform
        (RandomSystems.Applications.XoP.Model.outputMap inputs)
        (RandomSystems.Applications.XoP.Model.xopIdealPDS
          (G := G) (q := q)).dist := by
  simp [RandomSystems.Applications.XoP.Model.xopIdealPDS,
    RandomSystems.Instances.URFfun, RandomSystems.Instances.URFfunOf]
  rw [Dist.fTransform_comp]
  congr 1

/-- Every real CR18 system rectangle agrees with the honest real lazy
representative.  This is the real marginal theorem at the factor level. -/
private theorem xop_system_factor_eq_position_tape
    {q : Nat} (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G)
    (xv yv : List.Vector G q) :
    PFunPDE.transcriptSystemFactor (xop G)
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv =
      PFunPDE.transcriptSystemFactor
        (position_tape_prob G (real_fresh_tape G xs))
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv := by
  -- Expose the modern real rectangle as the literal-sum output-vector law.
  rw [xop_system_factor_eq_output_law]
  -- Transport literal sum to the normalized legacy coordinates.
  rw [sum_output_law_eq_legacy_normalized]
  -- Repackage the output vector as its canonical fixed-input transcript.
  rw [← legacy_transcript_apply_eq_output_law]
  -- Expose the target CR18 rectangle as the matching legacy position-tape
  -- transcript mass and identify its tape law.
  rw [position_tape_system_factor_eq_legacy_transcript]
  rw [real_fresh_tape_eq_legacy_real_visible G xs hq]
  exact congrArg
    (fun D : Dist (RandomSystems.Transcript G G q) =>
      D (RandomSystems.Transcript.ofOutputs
        (functionOfVector xv) (functionOfVector yv)))
    (legacy_real_transcript_eq_position_tape G
      (functionOfVector xv) hq)

/-- Every ideal CR18 system rectangle agrees with the honest uniform lazy
representative.  This is the ideal marginal theorem at the factor level. -/
private theorem urf_system_factor_eq_position_tape
    {q : Nat} (xv yv : List.Vector G q) :
    PFunPDE.transcriptSystemFactor (urf G)
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv =
      PFunPDE.transcriptSystemFactor
        (position_tape_prob G (ideal_fresh_tape G q))
        ((fun s : PFunDDS.DDS G G => s) :
          PFunPDS.RV (PFunDDS.DDS G G) G G) xv yv := by
  -- The ideal rectangle is uniform-function evaluation in both modern and
  -- legacy presentations.
  rw [urf_system_factor_eq_output_law]
  rw [urf_output_law_eq_legacy_ideal]
  -- As in the real proof, pass through the canonical fixed-input transcript
  -- and then use the all-input position-tape marginal.
  rw [← legacy_transcript_apply_eq_output_law]
  rw [position_tape_system_factor_eq_legacy_transcript]
  change
    (RandomSystems.Applications.XoP.Model.xopIdealPDS
      (G := G) (q := q)).transcriptDist (functionOfVector xv)
        (RandomSystems.Transcript.ofOutputs
          (functionOfVector xv) (functionOfVector yv)) =
      (RandomSystems.PDS.ofPositionTapeDist
        (q := q) (X := G) (Dist.uniform (Fin q → G))).transcriptDist
        (functionOfVector xv)
        (RandomSystems.Transcript.ofOutputs
          (functionOfVector xv) (functionOfVector yv))
  exact congrArg
    (fun D : Dist (RandomSystems.Transcript G G q) =>
      D (RandomSystems.Transcript.ofOutputs
        (functionOfVector xv) (functionOfVector yv)))
    (legacy_ideal_transcript_eq_position_tape G (functionOfVector xv))

/-- The real oracle and its lazy tape representative have identical
length-`q` transcript laws against every deterministic adaptive environment. -/
private theorem xop_transcript_eq_position_tape
    {q : Nat} (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G)
    (E : PFunDDS.DDE G G) :
    PFunPDS.Prob.deterministicTranscriptDist (q := q) (xop G) E =
      PFunPDS.Prob.deterministicTranscriptDist (q := q)
        (position_tape_prob G (real_fresh_tape G xs)) E :=
  deterministic_transcript_dist_eq_of_system_factor_eq
    (xop G) (position_tape_prob G (real_fresh_tape G xs))
    (xop_system_factor_eq_position_tape G hq xs) E

/-- The ideal oracle and its uniform lazy tape representative have identical
length-`q` transcript laws against every deterministic adaptive environment. -/
private theorem urf_transcript_eq_position_tape
    {q : Nat} (E : PFunDDS.DDE G G) :
    PFunPDS.Prob.deterministicTranscriptDist (q := q) (urf G) E =
      PFunPDS.Prob.deterministicTranscriptDist (q := q)
        (position_tape_prob G (ideal_fresh_tape G q)) E :=
  deterministic_transcript_dist_eq_of_system_factor_eq
    (urf G) (position_tape_prob G (ideal_fresh_tape G q))
    (urf_system_factor_eq_position_tape G) E

/-!
## 3. Exact maximal-coupling theorem

### The maximal coupling

We now couple the two honest tape laws themselves.  The generic finite
maximal-coupling construction is the overlap-plus-residual transport from the
paper: it places `min(P y, Q y)` on the diagonal and transports the two
disjoint residual laws off the diagonal.  Pushing this joint law through the
lazy-system map gives a coupling of honest CR18 representatives; pushing it
through deterministic replay gives a transcript coupling for each adaptive
environment.
-/

/-- A maximal coupling of the real and ideal fresh-output tapes. -/
noncomputable def maximal_tape_coupling {q : Nat} (xs : Fin q ↪ G) :
    DistCoupling (real_fresh_tape G xs).val (ideal_fresh_tape G q).val :=
  Common.TapeRepresentative.maximal_coupling
    (real_fresh_tape G xs) (ideal_fresh_tape G q)

/-- The first marginal of the maximal tape coupling is the real tape law. -/
theorem maximal_tape_coupling_fst {q : Nat} (xs : Fin q ↪ G) :
    Dist.fTransform Prod.fst (maximal_tape_coupling G xs).joint =
      (real_fresh_tape G xs).val :=
  Common.TapeRepresentative.maximal_coupling_fst
    (real_fresh_tape G xs) (ideal_fresh_tape G q)

/-- The second marginal of the maximal tape coupling is the ideal tape law. -/
theorem maximal_tape_coupling_snd {q : Nat} (xs : Fin q ↪ G) :
    Dist.fTransform Prod.snd (maximal_tape_coupling G xs).joint =
      (ideal_fresh_tape G q).val :=
  Common.TapeRepresentative.maximal_coupling_snd
    (real_fresh_tape G xs) (ideal_fresh_tape G q)

/-- The disagreement probability of the maximal tape coupling is exactly the
statistical distance of its two marginals. -/
theorem maximal_tape_coupling_disagreement {q : Nat} (xs : Fin q ↪ G) :
    (maximal_tape_coupling G xs).prDisagree =
      RandomSystems.statDist
        (real_fresh_tape G xs).val (ideal_fresh_tape G q).val :=
  Common.TapeRepresentative.maximal_coupling_disagreement
    (real_fresh_tape G xs) (ideal_fresh_tape G q)

/-- Event-mass spelling of the concrete tape disagreement, used only to
audit the subsequent pushforward to lazy systems. -/
private theorem maximal_tape_coupling_disagreement_eq_mass
    {q : Nat} (xs : Fin q ↪ G) :
    (maximal_tape_coupling G xs).prDisagree =
      (maximal_tape_coupling G xs).joint.mass
        (fun p => p.1 ≠ p.2) := by
  rw [Dist.mass_eq_sum, DistCoupling.prDisagree, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.1 ≠ p.2 <;> simp [h]

/-- The joint law obtained by applying the honest lazy-system map to both
coordinates of the maximal tape coupling.  We keep it as an explicit
finitely-supported joint law because the ambient CR18 DDS carrier need not
itself carry a `Fintype` instance. -/
noncomputable def maximal_lazy_system_joint {q : Nat}
    (xs : Fin q ↪ G) :
    Dist (PFunDDS.DDS G G × PFunDDS.DDS G G) :=
  Dist.fTransform
    (fun p : (Fin q → G) × (Fin q → G) =>
      (position_tape_dds G q p.1, position_tape_dds G q p.2))
    (maximal_tape_coupling G xs).joint

/-- The first marginal of the system joint is the honest real lazy
representative. -/
theorem maximal_lazy_system_joint_fst {q : Nat} (xs : Fin q ↪ G) :
    Dist.fTransform Prod.fst (maximal_lazy_system_joint G xs) =
      (position_tape_prob G (real_fresh_tape G xs)).val := by
  calc
    Dist.fTransform Prod.fst (maximal_lazy_system_joint G xs) =
        Dist.fTransform
          (position_tape_dds G q ∘ Prod.fst)
          (maximal_tape_coupling G xs).joint := by
            unfold maximal_lazy_system_joint
            rw [Dist.fTransform_comp]
            rfl
    _ = Dist.fTransform (position_tape_dds G q)
          (Dist.fTransform Prod.fst
            (maximal_tape_coupling G xs).joint) := by
            rw [Dist.fTransform_comp]
    _ = Dist.fTransform (position_tape_dds G q)
          (real_fresh_tape G xs).val := by
            rw [maximal_tape_coupling_fst]
    _ = (position_tape_prob G (real_fresh_tape G xs)).val := rfl

/-- The second marginal of the system joint is the honest ideal lazy
representative. -/
theorem maximal_lazy_system_joint_snd {q : Nat} (xs : Fin q ↪ G) :
    Dist.fTransform Prod.snd (maximal_lazy_system_joint G xs) =
      (position_tape_prob G (ideal_fresh_tape G q)).val := by
  calc
    Dist.fTransform Prod.snd (maximal_lazy_system_joint G xs) =
        Dist.fTransform
          (position_tape_dds G q ∘ Prod.snd)
          (maximal_tape_coupling G xs).joint := by
            unfold maximal_lazy_system_joint
            rw [Dist.fTransform_comp]
            rfl
    _ = Dist.fTransform (position_tape_dds G q)
          (Dist.fTransform Prod.snd
            (maximal_tape_coupling G xs).joint) := by
            rw [Dist.fTransform_comp]
    _ = Dist.fTransform (position_tape_dds G q)
          (ideal_fresh_tape G q).val := by
            rw [maximal_tape_coupling_snd]
    _ = (position_tape_prob G (ideal_fresh_tape G q)).val := rfl

/-- The system joint is normalized. -/
theorem maximal_lazy_system_joint_is_prob_dist {q : Nat}
    (xs : Fin q ↪ G) :
    (maximal_lazy_system_joint G xs).isProbDist := by
  constructor
  · exact (maximal_tape_coupling G xs).nonneg.fTransform _
  · calc
      (maximal_lazy_system_joint G xs).weight =
          (Dist.fTransform Prod.fst
            (maximal_lazy_system_joint G xs)).weight := by
              rw [Dist.weight_fTransform]
      _ = (position_tape_prob G (real_fresh_tape G xs)).val.weight := by
            rw [maximal_lazy_system_joint_fst]
      _ = 1 := (position_tape_prob G (real_fresh_tape G xs)).property.weight_eq

/-- Mapping tapes to honest lazy systems cannot create a disagreement, so the
system-level failure event is contained in the tape-level failure event. -/
theorem maximal_lazy_system_joint_disagreement_le {q : Nat}
    (xs : Fin q ↪ G) :
    (maximal_lazy_system_joint G xs).mass
        (fun p => p.1 ≠ p.2) ≤
      (maximal_tape_coupling G xs).prDisagree := by
  rw [maximal_tape_coupling_disagreement_eq_mass]
  unfold maximal_lazy_system_joint
  rw [Dist.mass_fTransform]
  apply Dist.mass_mono (maximal_tape_coupling G xs).nonneg
  intro p hp hEq
  exact hp (congrArg (position_tape_dds G q) hEq)

/-- Against any deterministic adaptive environment, the transcript distance
is bounded by the actual disagreement probability of the maximal tape
coupling. -/
theorem deterministic_transcript_distance_le_maximal_tape_disagreement
    {q : Nat} (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G)
    (E : PFunPDE.QQueryEnvironment G G q) :
    RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (xop G) E.1)
        (PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (urf G) E.1) ≤
      (maximal_tape_coupling G xs).prDisagree := by
  apply
    Common.TapeRepresentative.deterministic_transcript_distance_le_coupling
      (position_tape_representative G q)
      (xop G) (urf G)
      (real_fresh_tape G xs) (ideal_fresh_tape G q)
      (maximal_tape_coupling G xs) E
  · simpa [Common.TapeRepresentative.prob,
      position_tape_representative, position_tape_prob] using
      xop_transcript_eq_position_tape G hq xs E.1
  · simpa [Common.TapeRepresentative.prob,
      position_tape_representative, position_tape_prob] using
      urf_transcript_eq_position_tape G E.1

/-- Exact maximum adaptive distinguishing theorem before saturation.  A fixed
list of `q` distinct inputs converts the adaptive problem into the statistical
distance between the real and ideal fresh-output tapes. -/
theorem adv_prf_eq_fresh_tape_distance_of_le_card
    (q : Nat) (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) (xop G) (urf G) =
      (RandomSystems.statDist
        (Dist.fTransform
          (fun p : Equiv.Perm G × Equiv.Perm G =>
            fun i => xop_function G p (xs i))
          (Dist.uniform (Equiv.Perm G × Equiv.Perm G)))
        (Dist.uniform (Fin q → G)) : ℝ) := by
  apply le_antisymm
  · -- The shared representative theorem turns the concrete maximal tape
    -- coupling into a coupling bound for every adaptive environment.
    apply PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise_real
      (xop G) (urf G)
      (RandomSystems.statDist
        (real_fresh_tape G xs).val (ideal_fresh_tape G q).val)
      (RandomSystems.statDist_nonneg _ _)
    intro E
    rw [← maximal_tape_coupling_disagreement G xs]
    exact
      deterministic_transcript_distance_le_maximal_tape_disagreement
        G hq xs E
  · -- One fixed fresh schedule exposes the entire tape, so the same
    -- statistical distance is also attainable.
    apply
      Common.TapeRepresentative.tape_distance_le_adaptive_advantage_fixed_query
        (xop G) (urf G)
        (real_fresh_tape G xs) (ideal_fresh_tape G q) xs
    · exact
      PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
        ⟨Dist.uniform (Equiv.Perm G × Equiv.Perm G),
          Dist.uniform_isProbDist⟩
        (xop_function G) xs
    · change PFunPDS.Prob.fixedQueryTranscriptDist (urf G) xs =
        fixedInputLiftDist xs (Dist.uniform (Fin q → G))
      unfold urf
      rw [PFunPDS.Prob.fixedQueryTranscriptDist_urf,
        PFunPDS.uniformP_val,
        uniformFunction_eval_uniform xs xs.injective]

/-!
### Fiber formula

Only now, after the adaptive problem has been reduced to a finite tape
distance, do we introduce the compatible hidden-state count.  It is exactly
the fiber cardinality of the map from two injective permutation-image tapes
to their normalized visible output.  The literal-sum model reaches the same
fiber law through the proved negation transport above.
-/

/-- Number of injective hidden tapes `a` for which the shifted tape
`i ↦ a i + y i` is also injective. -/
def compatible_count {q : Nat} (y : Fin q → G) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter
    (fun a => Function.Injective a ∧
      Function.Injective (fun i => a i + y i))).card

/-- The local compatible count is the repository's generic compatible-fiber
count, with the defining predicates exposed. -/
private theorem compatible_count_eq_legacy {q : Nat} (y : Fin q → G) :
    compatible_count G y =
      RandomSystems.CompatibleCount.compatibleCountNat y := by
  unfold compatible_count
    RandomSystems.CompatibleCount.compatibleCountNat
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold RandomSystems.CompatibleCount.CompatibleHiddenState
    RandomSystems.CompatibleCount.shifted
  rfl

/-- Exact point mass of the real fresh-output tape. -/
theorem real_fresh_tape_apply {q : Nat} (hq : q ≤ Fintype.card G)
    (xs : Fin q ↪ G) (y : Fin q → G) :
    (real_fresh_tape G xs).val y =
      (compatible_count G y : Real) /
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : Real) := by
  -- Transport the public literal-sum tape to the counted visible law.
  rw [real_fresh_tape_eq_legacy_real_visible G xs hq]
  rw [RandomSystems.Applications.SoP.realVisibleDist_apply,
    RandomSystems.Applications.SoP.realVisibleMass_eq]
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  congr 1
  change
    (RandomSystems.CompatibleCount.compatibleCountNNReal y : Real) =
      (compatible_count G y : Real)
  rw [RandomSystems.CompatibleCount.compatibleCountNNReal_eq_coe_nat,
    ← compatible_count_eq_legacy G y]
  norm_cast

/-- Exact point mass of the ideal fresh-output tape. -/
theorem ideal_fresh_tape_apply {q : Nat} (y : Fin q → G) :
    (ideal_fresh_tape G q).val y =
      1 / ((Fintype.card G ^ q : Nat) : Real) := by
  change Dist.uniform (Fin q → G) y = _
  rw [Dist.uniform_apply, RandomSystems.CompatibleCount.visibleTupleCount_eq_pow]

/-- Total diagonal overlap between the real compatible-fiber law and the
uniform ideal law.  This is the success probability of a maximal tape
coupling. -/
noncomputable def compatible_overlap (q : Nat) : NNReal :=
  ∑ y : Fin q → G,
    min
      ((compatible_count G y : NNReal) /
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : NNReal))
      (1 / ((Fintype.card G ^ q : Nat) : NNReal))

/-- For normalized finite laws, statistical distance is one minus their
pointwise overlap.  Specialization of `statDist_eq_one_sub_sum_min`
(MaPiRe07 equation (3)) to `ProbDist` arguments. -/
private theorem stat_dist_eq_one_sub_sum_min
    {A : Type*} [Fintype A] (X Y : Dist.ProbDist A) :
    RandomSystems.statDist X.val Y.val =
      1 - ∑ a : A, min (X.val a) (Y.val a) :=
  RandomSystems.statDist_eq_one_sub_sum_min X.val Y.val X.property.weight_eq

/-- The explicit maximal tape coupling fails with probability exactly one
minus the compatible-fiber overlap. -/
theorem maximal_tape_coupling_disagreement_eq_one_sub_compatible_overlap
    {q : Nat} (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    (maximal_tape_coupling G xs).prDisagree =
      1 - compatible_overlap G q := by
  -- Maximality identifies disagreement with statistical distance, while the
  -- overlap identity identifies that distance with missing diagonal mass.
  rw [maximal_tape_coupling_disagreement G xs,
    stat_dist_eq_one_sub_sum_min
      (real_fresh_tape G xs) (ideal_fresh_tape G q)]
  have hoverlap :
      (compatible_overlap G q : Real) =
        ∑ y : Fin q → G,
          min ((real_fresh_tape G xs).val y)
            ((ideal_fresh_tape G q).val y) := by
    -- Substitute the two concrete point-mass formulas coordinate by
    -- coordinate.  No probabilistic or asymptotic estimate remains.
    unfold compatible_overlap
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [NNReal.coe_min]
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one]
    rw [real_fresh_tape_apply G hq xs y,
      ideal_fresh_tape_apply G y]
  rw [hoverlap]

/-- Compatible fibers partition the square of the injective-tape space. -/
theorem compatible_count_sum (q : Nat) :
    ∑ y : Fin q → G, compatible_count G y =
      (Fintype.card G).descFactorial q *
        (Fintype.card G).descFactorial q := by
  simpa [compatible_count_eq_legacy] using
    (RandomSystems.CompatibleCount.sum_compatibleCountNat_eq_descFactorial_sq
      (G := G) (q := q))

/-- On the unsaturated range, the exact maximum adaptive advantage is the
visible compatible-fiber statistical distance. -/
theorem adv_prf_eq_visible_stat_dist_of_le_card
    (q : Nat) (hq : q ≤ Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      (RandomSystems.Applications.SoP.visibleStatDist
        (G := G) (q := q) : ℝ) := by
  -- Choose any fresh schedule of the required length.
  obtain ⟨xs⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin q) (β := G) (by simpa using hq)
  rw [adv_prf_eq_fresh_tape_distance_of_le_card G q hq xs]
  change
    (RandomSystems.statDist
      (real_fresh_tape G xs).val (ideal_fresh_tape G q).val : ℝ) =
      (RandomSystems.Applications.SoP.visibleStatDist
        (G := G) (q := q) : ℝ)
  rw [real_fresh_tape_eq_legacy_real_visible G xs hq]
  rfl

/-- Exact compatible-count sum for the maximum adaptive advantage. -/
theorem sop_advantage_eq_compatible_count_distance_of_le_card
    (q : Nat) (hq : q ≤ Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      ((∑ y : Fin q → G,
        ((compatible_count G y : NNReal) /
            (((Fintype.card G).descFactorial q *
              (Fintype.card G).descFactorial q : Nat) : NNReal) -
          1 / ((Fintype.card G ^ q : Nat) : NNReal))) : NNReal) := by
  -- Expand the visible statistical distance and then substitute both exact
  -- point-mass formulas.
  rw [adv_prf_eq_visible_stat_dist_of_le_card G q hq]
  rw [RandomSystems.Applications.SoP.visibleStatDist_eq_sum]
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [NNReal.coe_sub_def]
  rw [RandomSystems.Applications.SoP.realVisibleMass_eq,
    RandomSystems.Applications.SoP.idealVisibleMass_eq]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one]
  change
    max
      ((RandomSystems.CompatibleCount.compatibleCountNNReal y : Real) / _ - _)
      0 = _
  rw [RandomSystems.CompatibleCount.compatibleCountNNReal_eq_coe_nat,
    ← compatible_count_eq_legacy G y]
  norm_cast

/-- Exact overlap form of the maximum adaptive advantage.  Equivalently, it
is exactly the disagreement probability of the maximal compatible-tape
coupling. -/
theorem sop_advantage_eq_one_sub_compatible_overlap_of_le_card
    (q : Nat) (hq : q ≤ Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      ((1 - compatible_overlap G q : NNReal) : ℝ) := by
  -- Choose a full fresh schedule and invoke the exact adaptive reduction.
  obtain ⟨xs⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin q) (β := G) (by simpa using hq)
  rw [adv_prf_eq_fresh_tape_distance_of_le_card G q hq xs]
  -- The tape distance is precisely the failure probability computed above.
  change
    RandomSystems.statDist
        (real_fresh_tape G xs).val (ideal_fresh_tape G q).val =
      ((1 - compatible_overlap G q : NNReal) : Real)
  have hoverlap_le : compatible_overlap G q ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_one]
    apply sub_nonneg.mp
    rw [← maximal_tape_coupling_disagreement_eq_one_sub_compatible_overlap
      G hq xs]
    exact (maximal_tape_coupling G xs).prDisagree_nonneg
  rw [← maximal_tape_coupling_disagreement G xs]
  rw [maximal_tape_coupling_disagreement_eq_one_sub_compatible_overlap
    G hq xs, NNReal.coe_sub hoverlap_le, NNReal.coe_one]

/-- Exact half-`L¹` form of the compatible-count characterization. -/
theorem sop_advantage_eq_half_l1_compatible_count_of_le_card
    (q : Nat) (hq : q ≤ Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      (1 / 2 : ℝ) *
        ∑ y : Fin q → G,
          |(((compatible_count G y : NNReal) /
              (((Fintype.card G).descFactorial q *
                (Fintype.card G).descFactorial q : Nat) : NNReal) :
              NNReal) : ℝ) -
            ((1 / ((Fintype.card G ^ q : Nat) : NNReal) : NNReal) : ℝ)| := by
  -- Reduce adaptivity to the two normalized fresh-tape laws.
  obtain ⟨xs⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin q) (β := G) (by simpa using hq)
  rw [adv_prf_eq_fresh_tape_distance_of_le_card G q hq xs]
  change
    (RandomSystems.statDist
      (real_fresh_tape G xs).val (ideal_fresh_tape G q).val : ℝ) = _
  -- Convert statistical distance to half-L¹, then expose the exact fibers.
  rw [coe_statDist_eq_half_sum_abs
    (real_fresh_tape G xs) (ideal_fresh_tape G q)]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [real_fresh_tape_apply G hq xs y,
    ideal_fresh_tape_apply G y]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one]

/-!
### Saturation at the size of the input space

When `q` exceeds `|G|`, a length-`q` uniform fresh tape is not an honest
random-function representative: there are only `|G|` possible fresh inputs.
The correct saturated object is the complete function table.  The generic
replay, maximal-coupling, and covering-schedule argument is proved once in
`Common`; this section only identifies the two concrete SoP2 table laws and
instantiates that result.
-/

/-- The law of the complete real function table. -/
private noncomputable def real_function_law : Dist.ProbDist (G → G) :=
  Common.induced_function_law
    ⟨Dist.uniform (Equiv.Perm G × Equiv.Perm G),
      Dist.uniform_isProbDist⟩
    (xop_function G)

/-- The law of the complete ideal function table. -/
private noncomputable def ideal_function_law : Dist.ProbDist (G → G) :=
  ⟨Dist.uniform (G → G), Dist.uniform_isProbDist⟩

/-- Sampling permutation pairs and then their sum is equivalent to sampling
the resulting complete function before embedding it as an evaluator. -/
private theorem xop_eq_function_evaluator_real_function_law :
    xop G =
      PFunPDS.Prob.functionEvaluator
        (real_function_law G) (fun f : G → G => f) := by
  exact
    Common.function_evaluator_eq_induced_function_law
      ⟨Dist.uniform (Equiv.Perm G × Equiv.Perm G),
        Dist.uniform_isProbDist⟩
      (xop_function G)

/-- The public ideal oracle is the evaluator of the uniform complete
function-table law. -/
private theorem urf_eq_function_evaluator_ideal_function_law :
    urf G =
      PFunPDS.Prob.functionEvaluator
        (ideal_function_law G) (fun f : G → G => f) := by
  apply Subtype.ext
  change
    Dist.fTransform (functionEvaluatorRV (fun f : G → G => f))
        (PFunPDS.uniformP (X := G) (Y := G)).val =
      Dist.fTransform (functionEvaluatorRV (fun f : G → G => f))
        (Dist.uniform (G → G))
  rw [PFunPDS.uniformP_val]

/-- Once the input space has been exhausted, the exact maximum adaptive
advantage is the complete-function-table distance. -/
private theorem adv_prf_eq_full_function_distance_of_card_le
    (q : Nat) (hq : Fintype.card G ≤ q) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      (RandomSystems.statDist
        (real_function_law G).val (ideal_function_law G).val : ℝ) := by
  rw [xop_eq_function_evaluator_real_function_law G,
    urf_eq_function_evaluator_ideal_function_law G]
  exact
    Common.adaptive_advantage_function_law_eq_stat_dist_of_card_le
      (real_function_law G) (ideal_function_law G) hq

/-- Exact all-budget theorem: the adaptive advantage saturates after
`min(q, |G|)` fresh queries. -/
theorem adv_prf_eq_visible_stat_dist_min_card (q : Nat) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      (RandomSystems.Applications.SoP.visibleStatDist
        (G := G) (q := min q (Fintype.card G)) : ℝ) := by
  rcases le_total q (Fintype.card G) with hq | hq
  · rw [Nat.min_eq_left hq]
    exact adv_prf_eq_visible_stat_dist_of_le_card G q hq
  · rw [Nat.min_eq_right hq]
    calc
      PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (xop G) (urf G) =
          (RandomSystems.statDist
            (real_function_law G).val
            (ideal_function_law G).val : ℝ) :=
        adv_prf_eq_full_function_distance_of_card_le G q hq
      _ = PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := Fintype.card G) (xop G) (urf G) :=
        (adv_prf_eq_full_function_distance_of_card_le
          G (Fintype.card G) le_rfl).symm
      _ = (RandomSystems.Applications.SoP.visibleStatDist
          (G := G) (q := Fintype.card G) : ℝ) :=
        adv_prf_eq_visible_stat_dist_of_le_card
          G (Fintype.card G) le_rfl

/-!
## 4. Audit and boundary results

### Exact audit cases

The first three query budgets are independent checks of normalization,
coercions, and saturation.  The visible-law computations below are purely
finite compatible-count identities; the adaptive conclusion continues to
come from the coupling reduction already proved above.
-/

/-- The visible statistical distance is the legacy file's explicit
compatible-count positive-error expression.  This local bridge is kept here
so the public endpoint does not become an alias of any legacy adaptive
theorem. -/
private theorem visible_stat_dist_eq_pure_visible_positive_error
    (q : Nat) (hq : q ≤ Fintype.card G) :
    RandomSystems.Applications.SoP.visibleStatDist
        (G := G) (q := q) =
      RandomSystems.Applications.XoP.Analytic.pureVisiblePositiveError
        (G := G) q := by
  apply NNReal.coe_injective
  rw [RandomSystems.Applications.SoP.visibleStatDist_eq_sum]
  simp [RandomSystems.Applications.XoP.Analytic.pureVisiblePositiveError,
    RandomSystems.Applications.SoP.realVisibleMass_eq_densityRatio_mul_ideal
      (G := G) (q := q) hq,
    RandomSystems.Applications.SoP.visibleDensityRatio,
    RandomSystems.Applications.SoP.expectationNormalizer_value,
    RandomSystems.Applications.SoP.idealVisibleMass]

/-- With no queries, the exact adaptive advantage is zero. -/
theorem sop_advantage_zero :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 0) (xop G) (urf G) = 0 := by
  rw [adv_prf_eq_visible_stat_dist_of_le_card
      G 0 (Nat.zero_le _),
    visible_stat_dist_eq_pure_visible_positive_error
      G 0 (Nat.zero_le _),
    RandomSystems.Applications.XoP.Analytic.pureVisiblePositiveError_zero]
  norm_num

/-- With one query, the exact adaptive advantage is zero. -/
theorem sop_advantage_one :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 1) (xop G) (urf G) = 0 := by
  have hG : 1 ≤ Fintype.card G := Fintype.card_pos
  rw [adv_prf_eq_visible_stat_dist_of_le_card G 1 hG,
    visible_stat_dist_eq_pure_visible_positive_error G 1 hG,
    RandomSystems.Applications.XoP.Analytic.pureVisiblePositiveError_one]
  norm_num

/-- Joint paper-facing statement of the zero- and one-query audit cases. -/
theorem sop_advantage_zero_one :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := 0) (xop G) (urf G) = 0 ∧
      PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := 1) (xop G) (urf G) = 0 :=
  ⟨sop_advantage_zero G, sop_advantage_one G⟩

/-- Exact two-query adaptive advantage. -/
theorem sop_advantage_two (hG : 2 ≤ Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 2) (xop G) (urf G) =
      ((1 /
        ((Fintype.card G : NNReal) *
          ((Fintype.card G - 1 : Nat) : NNReal)) : NNReal) : ℝ) := by
  rw [adv_prf_eq_visible_stat_dist_of_le_card G 2 hG,
    visible_stat_dist_eq_pure_visible_positive_error G 2 hG,
    RandomSystems.Applications.XoP.Analytic.pureVisiblePositiveError_two
      (G := G) hG]

/-!
### Exact three-query classification

The following finite calculation is an independent normalization audit of the
coupling theorem.  Its support lemmas remain private: public statements at the
end of the section mention only adaptive distinguishing advantage and the
cardinality of the group.

The proof first counts the three possible pair-collision sets among hidden
injective triples.  It then applies inclusion-exclusion, partitions visible
triples by equality pattern, and evaluates the resulting three masses.
-/

section ExactThreeQueryCombinatorics

variable {G : Type*} [Fintype G] [AddGroup G]

private def solve_right (x u v : G) : G := (x + u) - v

private theorem solve_right_add (x u v : G) :
    solve_right x u v + v = x + u := by
  simp [solve_right, sub_eq_add_neg, add_assoc]

private theorem solve_right_ne (x : G) {u v : G} (huv : u ≠ v) :
    solve_right x u v ≠ x := by
  intro h
  apply huv
  apply add_left_cancel (a := x)
  calc
    x + u = solve_right x u v + v := (solve_right_add x u v).symm
    _ = x + v := by rw [h]

private theorem card_filter_ne_ne (u v : G) (huv : u ≠ v) :
    ((Finset.univ : Finset G).filter (fun z => z ≠ u ∧ z ≠ v)).card =
      Fintype.card G - 2 := by
  classical
  have huv_mem : v ∈ (Finset.univ : Finset G).erase u := by
    simp [huv.symm]
  calc
    ((Finset.univ : Finset G).filter (fun z => z ≠ u ∧ z ≠ v)).card =
        (((Finset.univ : Finset G).erase u).erase v).card := by
          congr 1
          ext z
          simp [and_comm]
    _ = ((Finset.univ : Finset G).erase u).card - 1 :=
      Finset.card_erase_of_mem huv_mem
    _ = (Fintype.card G - 1) - 1 := by simp
    _ = Fintype.card G - 2 := by omega

set_option maxRecDepth 10000 in
private def collision01_equiv (u v : G) (huv : u ≠ v) :
    {a : Fin 3 → G //
      Function.Injective a ∧ a 0 + u = a 1 + v} ≃
      Σ x : G, {z : G // z ≠ x ∧ z ≠ solve_right x u v} where
  toFun a :=
    ⟨a.1 0, ⟨a.1 2, by
      have hsolve : a.1 1 = solve_right (a.1 0) u v := by
        apply add_right_cancel (b := v)
        rw [solve_right_add]
        exact a.2.2.symm
      constructor
      · intro h
        have hij : (2 : Fin 3) = 0 := a.2.1 h
        omega
      · intro h
        have hij : (2 : Fin 3) = 1 := a.2.1 (h.trans hsolve.symm)
        omega⟩⟩
  invFun p :=
    ⟨![p.1, solve_right p.1 u v, p.2.1], by
      constructor
      · have hd0 : solve_right p.1 u v ≠ p.1 :=
          solve_right_ne p.1 huv
        have hz0 : p.2.1 ≠ p.1 := p.2.2.1
        have hzd : p.2.1 ≠ solve_right p.1 u v := p.2.2.2
        intro i j h
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hd0 h.symm).elim
        · exact (hz0 h.symm).elim
        · exact (hd0 h).elim
        · rfl
        · exact (hzd h.symm).elim
        · exact (hz0 h).elim
        · exact (hzd h).elim
        · rfl
      · simp [solve_right_add]⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
    apply add_right_cancel (b := v)
    rw [solve_right_add]
    exact a.2.2
  right_inv p := by
    apply Sigma.ext rfl
    rfl

private theorem card_collision01 (u v : G) (huv : u ≠ v) :
    Fintype.card {a : Fin 3 → G //
      Function.Injective a ∧ a 0 + u = a 1 + v} =
      Fintype.card G * (Fintype.card G - 2) := by
  classical
  rw [Fintype.card_congr (collision01_equiv (G := G) u v huv)]
  rw [Fintype.card_sigma]
  calc
    ∑ x : G, Fintype.card
          {z : G // z ≠ x ∧ z ≠ solve_right x u v} =
        ∑ _x : G, (Fintype.card G - 2) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Fintype.card_subtype]
          exact card_filter_ne_ne x (solve_right x u v)
            (solve_right_ne x huv).symm
    _ = Fintype.card G * (Fintype.card G - 2) := by
      simp

private theorem injective_fin_three_iff (a : Fin 3 → G) :
    Function.Injective a ↔
      a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 ≠ a 2 := by
  constructor
  · intro ha
    exact ⟨fun h => by
      have := ha h
      omega,
      fun h => by
        have := ha h
        omega,
      fun h => by
        have := ha h
        omega⟩
  · rintro ⟨h01, h02, h12⟩ i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h01 h).elim
    · exact (h02 h).elim
    · exact (h01 h.symm).elim
    · rfl
    · exact (h12 h).elim
    · exact (h02 h.symm).elim
    · exact (h12 h.symm).elim
    · rfl

private def collision02_to_01_equiv (u v : G) :
    {a : Fin 3 → G //
      Function.Injective a ∧ a 0 + u = a 2 + v} ≃
      {a : Fin 3 → G //
        Function.Injective a ∧ a 0 + u = a 1 + v} where
  toFun a :=
    ⟨![a.1 0, a.1 2, a.1 1], by
      constructor
      · have ha := (injective_fin_three_iff a.1).mp a.2.1
        rw [injective_fin_three_iff]
        exact ⟨ha.2.1, ha.1, ha.2.2.symm⟩
      · exact a.2.2⟩
  invFun a :=
    ⟨![a.1 0, a.1 2, a.1 1], by
      constructor
      · have ha := (injective_fin_three_iff a.1).mp a.2.1
        rw [injective_fin_three_iff]
        exact ⟨ha.2.1, ha.1, ha.2.2.symm⟩
      · exact a.2.2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

private def collision12_to_01_equiv (u v : G) :
    {a : Fin 3 → G //
      Function.Injective a ∧ a 1 + u = a 2 + v} ≃
      {a : Fin 3 → G //
        Function.Injective a ∧ a 0 + u = a 1 + v} where
  toFun a :=
    ⟨![a.1 1, a.1 2, a.1 0], by
      constructor
      · have ha := (injective_fin_three_iff a.1).mp a.2.1
        rw [injective_fin_three_iff]
        exact ⟨ha.2.2, ha.1.symm, ha.2.1.symm⟩
      · exact a.2.2⟩
  invFun a :=
    ⟨![a.1 2, a.1 0, a.1 1], by
      constructor
      · have ha := (injective_fin_three_iff a.1).mp a.2.1
        rw [injective_fin_three_iff]
        exact ⟨ha.2.1.symm, ha.2.2.symm, ha.1⟩
      · exact a.2.2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

private theorem card_collision02 (u v : G) (huv : u ≠ v) :
    Fintype.card {a : Fin 3 → G //
      Function.Injective a ∧ a 0 + u = a 2 + v} =
      Fintype.card G * (Fintype.card G - 2) := by
  rw [Fintype.card_congr (collision02_to_01_equiv (G := G) u v)]
  exact card_collision01 u v huv

private theorem card_collision12 (u v : G) (huv : u ≠ v) :
    Fintype.card {a : Fin 3 → G //
      Function.Injective a ∧ a 1 + u = a 2 + v} =
      Fintype.card G * (Fintype.card G - 2) := by
  rw [Fintype.card_congr (collision12_to_01_equiv (G := G) u v)]
  exact card_collision01 u v huv

private def injective_three_set : Finset (Fin 3 → G) :=
  Finset.univ.filter Function.Injective

private def collision01_set (y : Fin 3 → G) : Finset (Fin 3 → G) :=
  Finset.univ.filter
    (fun a => Function.Injective a ∧ a 0 + y 0 = a 1 + y 1)

private def collision02_set (y : Fin 3 → G) : Finset (Fin 3 → G) :=
  Finset.univ.filter
    (fun a => Function.Injective a ∧ a 0 + y 0 = a 2 + y 2)

private def collision12_set (y : Fin 3 → G) : Finset (Fin 3 → G) :=
  Finset.univ.filter
    (fun a => Function.Injective a ∧ a 1 + y 1 = a 2 + y 2)

private def triple_collision_set (y : Fin 3 → G) : Finset (Fin 3 → G) :=
  Finset.univ.filter
    (fun a => Function.Injective a ∧
      a 0 + y 0 = a 1 + y 1 ∧
      a 0 + y 0 = a 2 + y 2)

private theorem injective_three_set_card :
    (injective_three_set (G := G)).card =
      (Fintype.card G).descFactorial 3 := by
  unfold injective_three_set
  letI : Fintype {f : Fin 3 → G // Function.Injective f} :=
    Fintype.ofEquiv (Fin 3 ↪ G)
      (Equiv.subtypeInjectiveEquivEmbedding (Fin 3) G).symm
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr
    (Equiv.subtypeInjectiveEquivEmbedding (Fin 3) G)]
  rw [Fintype.card_embedding_eq, Fintype.card_fin]

private theorem collision01_set_card (y : Fin 3 → G)
    (hy : y 0 ≠ y 1) :
    (collision01_set y).card =
      Fintype.card G * (Fintype.card G - 2) := by
  unfold collision01_set
  rw [← Fintype.card_subtype]
  exact card_collision01 (y 0) (y 1) hy

private theorem collision02_set_card (y : Fin 3 → G)
    (hy : y 0 ≠ y 2) :
    (collision02_set y).card =
      Fintype.card G * (Fintype.card G - 2) := by
  unfold collision02_set
  rw [← Fintype.card_subtype]
  exact card_collision02 (y 0) (y 2) hy

private theorem collision12_set_card (y : Fin 3 → G)
    (hy : y 1 ≠ y 2) :
    (collision12_set y).card =
      Fintype.card G * (Fintype.card G - 2) := by
  unfold collision12_set
  rw [← Fintype.card_subtype]
  exact card_collision12 (y 1) (y 2) hy

private theorem collision01_set_eq_empty (y : Fin 3 → G)
    (hy : y 0 = y 1) :
    collision01_set y = ∅ := by
  unfold collision01_set
  rw [Finset.filter_eq_empty_iff]
  intro a _ha ha
  apply Fin.zero_ne_one
  apply ha.1
  apply add_right_cancel (b := y 1)
  simpa [hy] using ha.2

private theorem collision02_set_eq_empty (y : Fin 3 → G)
    (hy : y 0 = y 2) :
    collision02_set y = ∅ := by
  unfold collision02_set
  rw [Finset.filter_eq_empty_iff]
  intro a _ha ha
  have hidx : (0 : Fin 3) = 2 := by
    apply ha.1
    apply add_right_cancel (b := y 2)
    simpa [hy] using ha.2
  omega

private theorem collision12_set_eq_empty (y : Fin 3 → G)
    (hy : y 1 = y 2) :
    collision12_set y = ∅ := by
  unfold collision12_set
  rw [Finset.filter_eq_empty_iff]
  intro a _ha ha
  have hidx : (1 : Fin 3) = 2 := by
    apply ha.1
    apply add_right_cancel (b := y 2)
    simpa [hy] using ha.2
  omega

private def solve_from_right (z y : G) : G := z - y

private theorem solve_from_right_add (z y : G) :
    solve_from_right z y + y = z := by
  simp [solve_from_right, sub_eq_add_neg, add_assoc]

private theorem solve_from_right_ne (z : G) {u v : G} (huv : u ≠ v) :
    solve_from_right z u ≠ solve_from_right z v := by
  intro h
  apply huv
  have hn : -u = -v := by
    apply add_left_cancel (a := z)
    simpa [solve_from_right, sub_eq_add_neg] using h
  exact neg_injective hn

private def triple_collision_equiv (y : Fin 3 → G)
    (h01 : y 0 ≠ y 1) (h02 : y 0 ≠ y 2) (h12 : y 1 ≠ y 2) :
    {a : Fin 3 → G //
      Function.Injective a ∧
        a 0 + y 0 = a 1 + y 1 ∧
        a 0 + y 0 = a 2 + y 2} ≃ G where
  toFun a := a.1 0 + y 0
  invFun z :=
    ⟨![solve_from_right z (y 0), solve_from_right z (y 1),
        solve_from_right z (y 2)], by
      constructor
      · rw [injective_fin_three_iff]
        exact ⟨solve_from_right_ne z h01,
          solve_from_right_ne z h02,
          solve_from_right_ne z h12⟩
      · change
          solve_from_right z (y 0) + y 0 =
              solve_from_right z (y 1) + y 1 ∧
            solve_from_right z (y 0) + y 0 =
              solve_from_right z (y 2) + y 2
        rw [solve_from_right_add, solve_from_right_add, solve_from_right_add]
        exact ⟨rfl, rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i
    · change
        solve_from_right (a.1 0 + y 0) (y 0) = a.1 0
      apply add_right_cancel (b := y 0)
      rw [solve_from_right_add]
    · change
        solve_from_right (a.1 0 + y 0) (y 1) = a.1 1
      apply add_right_cancel (b := y 1)
      rw [solve_from_right_add]
      exact a.2.2.1
    · change
        solve_from_right (a.1 0 + y 0) (y 2) = a.1 2
      apply add_right_cancel (b := y 2)
      rw [solve_from_right_add]
      exact a.2.2.2
  right_inv z := solve_from_right_add z (y 0)

private theorem triple_collision_set_card (y : Fin 3 → G)
    (h01 : y 0 ≠ y 1) (h02 : y 0 ≠ y 2) (h12 : y 1 ≠ y 2) :
    (triple_collision_set y).card = Fintype.card G := by
  unfold triple_collision_set
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    (triple_collision_equiv y h01 h02 h12)

private theorem collision01_inter_collision02 (y : Fin 3 → G) :
    collision01_set y ∩ collision02_set y = triple_collision_set y := by
  ext a
  simp only [collision01_set, collision02_set, triple_collision_set,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  aesop

private theorem collision01_inter_collision12 (y : Fin 3 → G) :
    collision01_set y ∩ collision12_set y = triple_collision_set y := by
  ext a
  simp only [collision01_set, collision12_set, triple_collision_set,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨ha, h01⟩, _ha, h12⟩
    exact ⟨ha, h01, h01.trans h12⟩
  · rintro ⟨ha, h01, h02⟩
    exact ⟨⟨ha, h01⟩, ha, h01.symm.trans h02⟩

private theorem collision02_inter_collision12 (y : Fin 3 → G) :
    collision02_set y ∩ collision12_set y = triple_collision_set y := by
  ext a
  simp only [collision02_set, collision12_set, triple_collision_set,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨ha, h02⟩, _ha, h12⟩
    exact ⟨ha, h02.trans h12.symm, h02⟩
  · rintro ⟨ha, h01, h02⟩
    exact ⟨⟨ha, h02⟩, ha, h01.symm.trans h02⟩

private def bad_collision_set (y : Fin 3 → G) : Finset (Fin 3 → G) :=
  collision01_set y ∪ collision02_set y ∪ collision12_set y

private theorem bad_collision_set_subset_injective_three_set (y : Fin 3 → G) :
    bad_collision_set y ⊆ injective_three_set := by
  intro a ha
  simp only [bad_collision_set, Finset.mem_union] at ha
  simp only [collision01_set, collision02_set, collision12_set,
    Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [injective_three_set, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rcases ha with (ha | ha) | ha
  · exact ha.1
  · exact ha.1
  · exact ha.1

private theorem compatible_count_nat_eq_injective_sdiff_bad
    (y : Fin 3 → G) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      (injective_three_set \ bad_collision_set y).card := by
  unfold RandomSystems.CompatibleCount.compatibleCountNat
    RandomSystems.CompatibleCount.CompatibleHiddenState
    RandomSystems.CompatibleCount.shifted
  apply congrArg Finset.card
  ext a
  simp only [injective_three_set, bad_collision_set, collision01_set,
    collision02_set, collision12_set, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union, not_or]
  rw [injective_fin_three_iff a,
    injective_fin_three_iff (fun i => a i + y i)]
  tauto

private theorem triple_collision_set_eq_empty_of_01
    (y : Fin 3 → G) (hy : y 0 = y 1) :
    triple_collision_set y = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [Finset.card_eq_zero]
  unfold triple_collision_set
  rw [Finset.filter_eq_empty_iff]
  intro a _ha ha
  apply Fin.zero_ne_one
  apply ha.1
  apply add_right_cancel (b := y 1)
  simpa [hy] using ha.2.1

private theorem triple_collision_set_eq_empty_of_02
    (y : Fin 3 → G) (hy : y 0 = y 2) :
    triple_collision_set y = ∅ := by
  unfold triple_collision_set
  rw [Finset.filter_eq_empty_iff]
  intro a _ha ha
  have hidx : (0 : Fin 3) = 2 := by
    apply ha.1
    apply add_right_cancel (b := y 2)
    simpa [hy] using ha.2.2
  omega

private theorem triple_collision_set_eq_empty_of_12
    (y : Fin 3 → G) (hy : y 1 = y 2) :
    triple_collision_set y = ∅ := by
  unfold triple_collision_set
  rw [Finset.filter_eq_empty_iff]
  intro a _ha ha
  have hshift : a 1 + y 1 = a 2 + y 2 :=
    ha.2.1.symm.trans ha.2.2
  have hidx : (1 : Fin 3) = 2 := by
    apply ha.1
    apply add_right_cancel (b := y 2)
    simpa [hy] using hshift
  omega

private theorem bad_collision_set_card_eq_two_events_of_01
    (y : Fin 3 → G) (h01 : y 0 = y 1)
    (h02 : y 0 ≠ y 2) :
    (bad_collision_set y).card =
      2 * (Fintype.card G * (Fintype.card G - 2)) := by
  have h12 : y 1 ≠ y 2 := by simpa [h01] using h02
  have hdisj : Disjoint (collision02_set y) (collision12_set y) := by
    rw [Finset.disjoint_iff_inter_eq_empty,
      collision02_inter_collision12,
      triple_collision_set_eq_empty_of_01 y h01]
  rw [bad_collision_set, collision01_set_eq_empty y h01,
    Finset.empty_union, Finset.card_union_of_disjoint hdisj,
    collision02_set_card y h02, collision12_set_card y h12]
  omega

private theorem bad_collision_set_card_eq_two_events_of_02
    (y : Fin 3 → G) (h02 : y 0 = y 2)
    (h01 : y 0 ≠ y 1) :
    (bad_collision_set y).card =
      2 * (Fintype.card G * (Fintype.card G - 2)) := by
  have h12 : y 1 ≠ y 2 := by
    intro h
    exact h01 (h02.trans h.symm)
  have hdisj : Disjoint (collision01_set y) (collision12_set y) := by
    rw [Finset.disjoint_iff_inter_eq_empty,
      collision01_inter_collision12,
      triple_collision_set_eq_empty_of_02 y h02]
  rw [bad_collision_set, collision02_set_eq_empty y h02,
    Finset.union_empty, Finset.card_union_of_disjoint hdisj,
    collision01_set_card y h01, collision12_set_card y h12]
  omega

private theorem bad_collision_set_card_eq_two_events_of_12
    (y : Fin 3 → G) (h12 : y 1 = y 2)
    (h01 : y 0 ≠ y 1) :
    (bad_collision_set y).card =
      2 * (Fintype.card G * (Fintype.card G - 2)) := by
  have h02 : y 0 ≠ y 2 := by simpa [h12] using h01
  have hdisj : Disjoint (collision01_set y) (collision02_set y) := by
    rw [Finset.disjoint_iff_inter_eq_empty,
      collision01_inter_collision02,
      triple_collision_set_eq_empty_of_12 y h12]
  rw [bad_collision_set, collision12_set_eq_empty y h12,
    Finset.union_empty, Finset.card_union_of_disjoint hdisj,
    collision01_set_card y h01, collision02_set_card y h02]
  omega

private theorem union01_02_inter_12 (y : Fin 3 → G) :
    (collision01_set y ∪ collision02_set y) ∩ collision12_set y =
      triple_collision_set y := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, h12⟩
    · have ha : a ∈ collision01_set y ∩ collision12_set y := by
        exact Finset.mem_inter.mpr ⟨h, h12⟩
      rwa [collision01_inter_collision12] at ha
    · have ha : a ∈ collision02_set y ∩ collision12_set y := by
        exact Finset.mem_inter.mpr ⟨h, h12⟩
      rwa [collision02_inter_collision12] at ha
  · intro ha
    have h01 : a ∈ collision01_set y ∩ collision12_set y := by
      rwa [collision01_inter_collision12]
    exact ⟨Or.inl (Finset.mem_inter.mp h01).1,
      (Finset.mem_inter.mp h01).2⟩

private theorem bad_collision_set_card_of_pairwise_ne
    (y : Fin 3 → G)
    (h01 : y 0 ≠ y 1) (h02 : y 0 ≠ y 2) (h12 : y 1 ≠ y 2) :
    (bad_collision_set y).card =
      3 * (Fintype.card G * (Fintype.card G - 2)) -
        2 * Fintype.card G := by
  rw [bad_collision_set, Finset.card_union, Finset.card_union,
    collision01_inter_collision02,
    union01_02_inter_12,
    collision01_set_card y h01,
    collision02_set_card y h02,
    collision12_set_card y h12,
    triple_collision_set_card y h01 h02 h12]
  omega

private theorem compatible_count_nat_all_equal
    (y : Fin 3 → G) (h01 : y 0 = y 1) (h02 : y 0 = y 2) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      (Fintype.card G).descFactorial 3 := by
  have h12 : y 1 = y 2 := h01.symm.trans h02
  rw [compatible_count_nat_eq_injective_sdiff_bad,
    bad_collision_set, collision01_set_eq_empty y h01,
    collision02_set_eq_empty y h02, collision12_set_eq_empty y h12]
  simp [injective_three_set_card]

private theorem compatible_count_nat_exact_two_of_bad_card
    (y : Fin 3 → G) (hN2 : 2 ≤ Fintype.card G)
    (hbad : (bad_collision_set y).card =
      2 * (Fintype.card G * (Fintype.card G - 2))) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      Fintype.card G * (Fintype.card G - 2) *
        (Fintype.card G - 3) := by
  let N := Fintype.card G
  by_cases hNeq : N = 2
  · rw [compatible_count_nat_eq_injective_sdiff_bad,
      Finset.card_sdiff_of_subset
        (bad_collision_set_subset_injective_three_set y),
      injective_three_set_card, hbad]
    change
      N.descFactorial 3 - 2 * (N * (N - 2)) =
        N * (N - 2) * (N - 3)
    simp [hNeq, Nat.descFactorial_succ]
  · have hN3 : 3 ≤ N := by omega
    have hNm1 : N - 1 = (N - 3) + 2 := by omega
    have hNm2 : N - 2 = (N - 3) + 1 := by omega
    have hsplit :
        (N - 2) * ((N - 1) * N) =
          N * (N - 2) * (N - 3) +
            2 * (N * (N - 2)) := by
      rw [hNm1, hNm2]
      ring
    rw [compatible_count_nat_eq_injective_sdiff_bad,
      Finset.card_sdiff_of_subset
        (bad_collision_set_subset_injective_three_set y),
      injective_three_set_card, hbad]
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.mul_one]
    change
      (N - 2) * ((N - 1) * N) - 2 * (N * (N - 2)) =
        N * (N - 2) * (N - 3)
    rw [hsplit, Nat.add_sub_cancel]

private theorem compatible_count_nat_exact_two_01
    (y : Fin 3 → G) (h01 : y 0 = y 1) (h02 : y 0 ≠ y 2) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      Fintype.card G * (Fintype.card G - 2) *
        (Fintype.card G - 3) := by
  have hN2 : 2 ≤ Fintype.card G := by
    have : 1 < Fintype.card G :=
      Fintype.one_lt_card_iff.mpr ⟨y 0, y 2, h02⟩
    omega
  exact compatible_count_nat_exact_two_of_bad_card y hN2
    (bad_collision_set_card_eq_two_events_of_01 y h01 h02)

private theorem compatible_count_nat_exact_two_02
    (y : Fin 3 → G) (h02 : y 0 = y 2) (h01 : y 0 ≠ y 1) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      Fintype.card G * (Fintype.card G - 2) *
        (Fintype.card G - 3) := by
  have hN2 : 2 ≤ Fintype.card G := by
    have : 1 < Fintype.card G :=
      Fintype.one_lt_card_iff.mpr ⟨y 0, y 1, h01⟩
    omega
  exact compatible_count_nat_exact_two_of_bad_card y hN2
    (bad_collision_set_card_eq_two_events_of_02 y h02 h01)

private theorem compatible_count_nat_exact_two_12
    (y : Fin 3 → G) (h12 : y 1 = y 2) (h01 : y 0 ≠ y 1) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      Fintype.card G * (Fintype.card G - 2) *
        (Fintype.card G - 3) := by
  have hN2 : 2 ≤ Fintype.card G := by
    have : 1 < Fintype.card G :=
      Fintype.one_lt_card_iff.mpr ⟨y 0, y 1, h01⟩
    omega
  exact compatible_count_nat_exact_two_of_bad_card y hN2
    (bad_collision_set_card_eq_two_events_of_12 y h12 h01)

private theorem compatible_count_nat_pairwise_ne
    (y : Fin 3 → G)
    (h01 : y 0 ≠ y 1) (h02 : y 0 ≠ y 2) (h12 : y 1 ≠ y 2) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      Fintype.card G *
        (Fintype.card G ^ 2 + 10 - 6 * Fintype.card G) := by
  let N := Fintype.card G
  have hyinj : Function.Injective y :=
    (injective_fin_three_iff y).mpr ⟨h01, h02, h12⟩
  have hN3 : 3 ≤ N := by
    simpa [N, Fintype.card_fin] using
      Fintype.card_le_of_injective y hyinj
  let k := N - 3
  have hN : N = k + 3 := by omega
  have hNm1 : N - 1 = k + 2 := by omega
  have hNm2 : N - 2 = k + 1 := by omega
  have htargetInner : N ^ 2 + 10 - 6 * N = k ^ 2 + 1 := by
    rw [Nat.sub_eq_iff_eq_add]
    · rw [hN]
      ring
    · rw [hN]
      nlinarith
  have hbad :
      3 * (N * (N - 2)) - 2 * N = N * (3 * k + 1) := by
    rw [Nat.sub_eq_iff_eq_add]
    · rw [hNm2, hN]
      ring
    · rw [hNm2, hN]
      nlinarith
  have hsplit :
      (N - 2) * ((N - 1) * N) =
        N * (k ^ 2 + 1) + N * (3 * k + 1) := by
    rw [hNm2, hNm1, hN]
    ring
  rw [compatible_count_nat_eq_injective_sdiff_bad,
    Finset.card_sdiff_of_subset
      (bad_collision_set_subset_injective_three_set y),
    injective_three_set_card,
    bad_collision_set_card_of_pairwise_ne y h01 h02 h12]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.mul_one]
  change
    (N - 2) * ((N - 1) * N) -
        (3 * (N * (N - 2)) - 2 * N) =
      N * (N ^ 2 + 10 - 6 * N)
  rw [hbad, hsplit, Nat.add_sub_cancel, htargetInner]

/-!
The hidden count is now classified by the equality pattern of the three
visible outputs.  This is the combinatorial heart of the exact audit: each
bad collision hyperplane has an explicit cardinality, and inclusion-exclusion
depends only on whether all, exactly two, or none of the outputs coincide.
-/
private theorem compatible_count_nat_fin_three_classification (y : Fin 3 → G) :
    RandomSystems.CompatibleCount.compatibleCountNat y =
      if y 0 = y 1 ∧ y 0 = y 2 then
        Fintype.card G * (Fintype.card G - 1) *
          (Fintype.card G - 2)
      else if y 0 = y 1 ∨ y 0 = y 2 ∨ y 1 = y 2 then
        Fintype.card G * (Fintype.card G - 2) *
          (Fintype.card G - 3)
      else
        Fintype.card G *
          (Fintype.card G ^ 2 + 10 - 6 * Fintype.card G) := by
  by_cases h01 : y 0 = y 1
  · by_cases h02 : y 0 = y 2
    · rw [if_pos ⟨h01, h02⟩]
      rw [compatible_count_nat_all_equal y h01 h02]
      simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
      ring
    · rw [if_neg (by tauto), if_pos (by tauto)]
      exact compatible_count_nat_exact_two_01 y h01 h02
  · by_cases h02 : y 0 = y 2
    · rw [if_neg (by tauto), if_pos (by tauto)]
      exact compatible_count_nat_exact_two_02 y h02 h01
    · by_cases h12 : y 1 = y 2
      · rw [if_neg (by tauto), if_pos (by tauto)]
        exact compatible_count_nat_exact_two_12 y h12 h01
      · rw [if_neg (by tauto), if_neg (by tauto)]
        exact compatible_count_nat_pairwise_ne y h01 h02 h12

/-!
The second part counts how many visible tapes have each equality pattern.
Together with the fiber classification, this converts the full finite
statistical-distance sum into three scalar contributions.
-/
private def all_equal_output_set : Finset (Fin 3 → G) :=
  Finset.univ.filter (fun y => y 0 = y 1 ∧ y 0 = y 2)

private def exactly_two_equal_output_set : Finset (Fin 3 → G) :=
  Finset.univ.filter (fun y =>
    ¬(y 0 = y 1 ∧ y 0 = y 2) ∧
      (y 0 = y 1 ∨ y 0 = y 2 ∨ y 1 = y 2))

private def pairwise_distinct_output_set : Finset (Fin 3 → G) :=
  Finset.univ.filter
    (fun y => y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 1 ≠ y 2)

private def all_equal_output_equiv :
    {y : Fin 3 → G // y 0 = y 1 ∧ y 0 = y 2} ≃ G where
  toFun y := y.1 0
  invFun g := ⟨fun _ => g, ⟨rfl, rfl⟩⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · exact y.2.1
    · exact y.2.2
  right_inv _ := rfl

private theorem all_equal_output_set_card :
    (all_equal_output_set (G := G)).card = Fintype.card G := by
  unfold all_equal_output_set
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (all_equal_output_equiv (G := G))

private theorem pairwise_distinct_output_set_card :
    (pairwise_distinct_output_set (G := G)).card =
      (Fintype.card G).descFactorial 3 := by
  unfold pairwise_distinct_output_set
  calc
    ((Finset.univ : Finset (Fin 3 → G)).filter
        (fun y => y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 1 ≠ y 2)).card =
        (injective_three_set (G := G)).card := by
          congr 1
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            injective_three_set]
          exact (injective_fin_three_iff y).symm
    _ = (Fintype.card G).descFactorial 3 := injective_three_set_card

private theorem output_pattern_partition :
    all_equal_output_set (G := G) ∪ exactly_two_equal_output_set ∪
        pairwise_distinct_output_set =
      Finset.univ := by
  ext y
  simp only [all_equal_output_set, exactly_two_equal_output_set,
    pairwise_distinct_output_set, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  tauto

private theorem all_equal_disjoint_exactly_two :
    Disjoint (all_equal_output_set (G := G)) exactly_two_equal_output_set := by
  rw [Finset.disjoint_left]
  intro y ha he
  simp only [all_equal_output_set, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha
  simp only [exactly_two_equal_output_set, Finset.mem_filter,
    Finset.mem_univ, true_and] at he
  exact he.1 ha

private theorem all_or_exact_disjoint_pairwise :
    Disjoint
      (all_equal_output_set (G := G) ∪ exactly_two_equal_output_set)
      pairwise_distinct_output_set := by
  rw [Finset.disjoint_left]
  intro y hae hp
  simp only [Finset.mem_union] at hae
  simp only [all_equal_output_set, exactly_two_equal_output_set,
    pairwise_distinct_output_set, Finset.mem_filter, Finset.mem_univ,
    true_and] at hae hp
  rcases hae with ha | he
  · exact hp.1 ha.1
  · rcases he.2 with h01 | h02 | h12
    · exact hp.1 h01
    · exact hp.2.1 h02
    · exact hp.2.2 h12

private theorem card_cube_pattern_identity (N : Nat) :
    N ^ 3 =
      N + 3 * N * (N - 1) +
        N.descFactorial 3 := by
  by_cases hN : 2 ≤ N
  · let k := N - 2
    have hN' : N = k + 2 := by omega
    have hNm1 : N - 1 = k + 1 := by omega
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.mul_one]
    rw [hNm1, hN']
    simp
    ring
  · interval_cases N <;> norm_num [Nat.descFactorial_succ]

private theorem exactly_two_equal_output_set_card :
    (exactly_two_equal_output_set (G := G)).card =
      3 * Fintype.card G * (Fintype.card G - 1) := by
  have hpartition_card :
      Fintype.card G ^ 3 =
        (all_equal_output_set (G := G)).card +
          (exactly_two_equal_output_set (G := G)).card +
            (pairwise_distinct_output_set (G := G)).card := by
    calc
      Fintype.card G ^ 3 =
          (Finset.univ : Finset (Fin 3 → G)).card := by simp
      _ = (all_equal_output_set (G := G) ∪ exactly_two_equal_output_set ∪
            pairwise_distinct_output_set).card := by
              rw [output_pattern_partition]
      _ = (all_equal_output_set (G := G) ∪
            exactly_two_equal_output_set).card +
          (pairwise_distinct_output_set (G := G)).card :=
            Finset.card_union_of_disjoint all_or_exact_disjoint_pairwise
      _ = ((all_equal_output_set (G := G)).card +
            (exactly_two_equal_output_set (G := G)).card) +
          (pairwise_distinct_output_set (G := G)).card := by
            rw [Finset.card_union_of_disjoint all_equal_disjoint_exactly_two]
  rw [all_equal_output_set_card, pairwise_distinct_output_set_card] at hpartition_card
  have hid := card_cube_pattern_identity (Fintype.card G)
  omega

private theorem sum_by_output_pattern (A E D : NNReal) :
    ∑ y : Fin 3 → G,
        (if y 0 = y 1 ∧ y 0 = y 2 then A
        else if y 0 = y 1 ∨ y 0 = y 2 ∨ y 1 = y 2 then E
        else D) =
      (Fintype.card G) • A +
        (3 * Fintype.card G * (Fintype.card G - 1)) • E +
        ((Fintype.card G).descFactorial 3) • D := by
  let f : (Fin 3 → G) → NNReal := fun y =>
    if y 0 = y 1 ∧ y 0 = y 2 then A
    else if y 0 = y 1 ∨ y 0 = y 2 ∨ y 1 = y 2 then E
    else D
  have hall :
      ∑ y ∈ all_equal_output_set (G := G), f y =
        (all_equal_output_set (G := G)).card • A := by
    apply Finset.sum_eq_card_nsmul
    intro y hy
    simp only [all_equal_output_set, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy
    rw [show f y = A by
      unfold f
      rw [if_pos hy]]
  have hexact :
      ∑ y ∈ exactly_two_equal_output_set (G := G), f y =
        (exactly_two_equal_output_set (G := G)).card • E := by
    apply Finset.sum_eq_card_nsmul
    intro y hy
    simp only [exactly_two_equal_output_set, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    rw [show f y = E by
      unfold f
      rw [if_neg hy.1, if_pos hy.2]]
  have hdistinct :
      ∑ y ∈ pairwise_distinct_output_set (G := G), f y =
        (pairwise_distinct_output_set (G := G)).card • D := by
    apply Finset.sum_eq_card_nsmul
    intro y hy
    simp only [pairwise_distinct_output_set, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    have hall_ne : ¬(y 0 = y 1 ∧ y 0 = y 2) := by tauto
    have hany_ne : ¬(y 0 = y 1 ∨ y 0 = y 2 ∨ y 1 = y 2) := by tauto
    rw [show f y = D by
      unfold f
      rw [if_neg hall_ne, if_neg hany_ne]]
  change ∑ y : Fin 3 → G, f y = _
  change Finset.sum (Finset.univ : Finset (Fin 3 → G)) f = _
  rw [← output_pattern_partition (G := G)]
  rw [Finset.sum_union all_or_exact_disjoint_pairwise,
    Finset.sum_union all_equal_disjoint_exactly_two]
  rw [hall, hexact, hdistinct, all_equal_output_set_card,
    exactly_two_equal_output_set_card, pairwise_distinct_output_set_card]

/-!
Finally we evaluate the positive part of the exact compatible-count distance.
The sign pattern changes at cardinality four, which is why the exact theorem
has separate branches for N = 3, N = 4, and N ≥ 5.
-/
private def q3_positive_error : NNReal :=
  ∑ y : Fin 3 → G,
    ((RandomSystems.CompatibleCount.compatibleCountNat y : NNReal) /
        (((Fintype.card G).descFactorial 3 *
          (Fintype.card G).descFactorial 3 : Nat) : NNReal) -
      1 / ((Fintype.card G ^ 3 : Nat) : NNReal))

private theorem q3_positive_error_eq_pattern :
    q3_positive_error (G := G) =
      (Fintype.card G) •
        (((Fintype.card G * (Fintype.card G - 1) *
            (Fintype.card G - 2) : Nat) : NNReal) /
            (((Fintype.card G).descFactorial 3 *
              (Fintype.card G).descFactorial 3 : Nat) : NNReal) -
          1 / ((Fintype.card G ^ 3 : Nat) : NNReal)) +
      (3 * Fintype.card G * (Fintype.card G - 1)) •
        (((Fintype.card G * (Fintype.card G - 2) *
            (Fintype.card G - 3) : Nat) : NNReal) /
            (((Fintype.card G).descFactorial 3 *
              (Fintype.card G).descFactorial 3 : Nat) : NNReal) -
          1 / ((Fintype.card G ^ 3 : Nat) : NNReal)) +
      ((Fintype.card G).descFactorial 3) •
        (((Fintype.card G *
            (Fintype.card G ^ 2 + 10 - 6 * Fintype.card G) : Nat) :
              NNReal) /
            (((Fintype.card G).descFactorial 3 *
              (Fintype.card G).descFactorial 3 : Nat) : NNReal) -
          1 / ((Fintype.card G ^ 3 : Nat) : NNReal)) := by
  let den : NNReal :=
    (((Fintype.card G).descFactorial 3 *
      (Fintype.card G).descFactorial 3 : Nat) : NNReal)
  let u : NNReal := 1 / ((Fintype.card G ^ 3 : Nat) : NNReal)
  let A : NNReal :=
    (((Fintype.card G * (Fintype.card G - 1) *
      (Fintype.card G - 2) : Nat) : NNReal) / den - u)
  let E : NNReal :=
    (((Fintype.card G * (Fintype.card G - 2) *
      (Fintype.card G - 3) : Nat) : NNReal) / den - u)
  let D : NNReal :=
    (((Fintype.card G *
      (Fintype.card G ^ 2 + 10 - 6 * Fintype.card G) : Nat) :
        NNReal) / den - u)
  unfold q3_positive_error
  change
    (∑ y : Fin 3 → G,
      ((RandomSystems.CompatibleCount.compatibleCountNat y : NNReal) /
        den - u)) =
      (Fintype.card G) • A +
        (3 * Fintype.card G * (Fintype.card G - 1)) • E +
        ((Fintype.card G).descFactorial 3) • D
  simp_rw [compatible_count_nat_fin_three_classification]
  calc
    _ =
        ∑ y : Fin 3 → G,
          (if y 0 = y 1 ∧ y 0 = y 2 then A
          else if y 0 = y 1 ∨ y 0 = y 2 ∨ y 1 = y 2 then E
          else D) := by
            apply Finset.sum_congr rfl
            intro y _hy
            split_ifs <;> rfl
    _ = _ := sum_by_output_pattern A E D

private theorem q3_positive_error_card_three (hG : Fintype.card G = 3) :
    q3_positive_error (G := G) = 2 / 3 := by
  rw [q3_positive_error_eq_pattern]
  have h16 : (1 / 27 : NNReal) ≤ 1 / 6 := by
    apply NNReal.coe_le_coe.mp
    norm_num
  have h112 : (1 / 27 : NNReal) ≤ 1 / 12 := by
    apply NNReal.coe_le_coe.mp
    norm_num
  norm_num [hG, Nat.descFactorial_succ]
  apply NNReal.eq
  push_cast
  rw [NNReal.coe_sub h16, NNReal.coe_sub h112]
  norm_num

private theorem q3_positive_error_card_four (hG : Fintype.card G = 4) :
    q3_positive_error (G := G) = 5 / 48 := by
  rw [q3_positive_error_eq_pattern]
  have h124 : (1 / 64 : NNReal) ≤ 1 / 24 := by
    apply NNReal.coe_le_coe.mp
    norm_num
  have hzero : (1 / 72 : NNReal) ≤ 1 / 64 := by
    apply NNReal.coe_le_coe.mp
    norm_num
  norm_num [hG, Nat.descFactorial_succ,
    tsub_eq_zero_of_le hzero]
  apply NNReal.eq
  push_cast
  rw [NNReal.coe_sub h124]
  norm_num

private theorem q3_positive_error_card_ge_five
    (hG : 5 ≤ Fintype.card G) :
    q3_positive_error (G := G) =
      (((3 * Fintype.card G ^ 2 + 4 -
        12 * Fintype.card G : Nat) : NNReal) /
        ((Fintype.card G ^ 2 * (Fintype.card G - 1) *
          (Fintype.card G - 2) : Nat) : NNReal)) := by
  rw [q3_positive_error_eq_pattern]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.mul_one, Nat.sub_zero]
  let N := Fintype.card G
  let F := N * (N - 1) * (N - 2)
  let C₂ := N * (N - 2) * (N - 3)
  let C₃ := N * (N ^ 2 + 10 - 6 * N)
  let T := 3 * N ^ 2 + 4 - 12 * N
  have hdesc : (N - 2) * ((N - 1) * N) = F := by
    simp [F]
    ring
  rw [hdesc]
  change
    N • (((F : Nat) : NNReal) / (((F * F : Nat) : NNReal)) -
          1 / (((N ^ 3 : Nat) : NNReal))) +
      (3 * N * (N - 1)) •
        (((C₂ : Nat) : NNReal) / (((F * F : Nat) : NNReal)) -
          1 / (((N ^ 3 : Nat) : NNReal))) +
      F • (((C₃ : Nat) : NNReal) / (((F * F : Nat) : NNReal)) -
          1 / (((N ^ 3 : Nat) : NNReal))) =
        ((T : Nat) : NNReal) /
          (((N ^ 2 * (N - 1) * (N - 2) : Nat) : NNReal))
  have hN5 : 5 ≤ N := by simpa [N] using hG
  have hN0 : 0 < N := by omega
  have hNm1pos : 0 < N - 1 := by omega
  have hNm2pos : 0 < N - 2 := by omega
  have hF0 : 0 < F := by
    exact Nat.mul_pos (Nat.mul_pos hN0 hNm1pos) hNm2pos
  have hP0 : 0 < N ^ 3 := pow_pos hN0 _
  have hF20 : 0 < F * F := Nat.mul_pos hF0 hF0
  let k := N - 5
  have hN : N = k + 5 := by omega
  have hNm1 : N - 1 = k + 4 := by omega
  have hNm2 : N - 2 = k + 3 := by omega
  have hNm3 : N - 3 = k + 2 := by omega
  have hCinner :
      N ^ 2 + 10 - 6 * N = k ^ 2 + 4 * k + 5 := by
    rw [Nat.sub_eq_iff_eq_add]
    · rw [hN]
      ring
    · rw [hN]
      nlinarith
  have hT :
      T = 3 * k ^ 2 + 18 * k + 19 := by
    dsimp [T]
    rw [Nat.sub_eq_iff_eq_add]
    · rw [hN]
      ring
    · rw [hN]
      nlinarith
  have hFle : F ≤ N ^ 3 := by
    simpa [F, Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.descFactorial_le_pow N 3)
  have hA_nat : F * F ≤ F * (N ^ 3) :=
    Nat.mul_le_mul_left F hFle
  have hE_core :
      (N - 1) ^ 2 * (N - 2) ≤ N ^ 2 * (N - 3) := by
    apply Nat.le.intro (k := k ^ 2 + 5 * k + 2)
    rw [hNm1, hNm2, hNm3, hN]
    ring
  have hE_nat : F * F ≤ C₂ * (N ^ 3) := by
    have hmul :=
      Nat.mul_le_mul_left (N ^ 2 * (N - 2)) hE_core
    calc
      F * F =
          (N ^ 2 * (N - 2)) * ((N - 1) ^ 2 * (N - 2)) := by
            simp [F]
            ring
      _ ≤ (N ^ 2 * (N - 2)) * (N ^ 2 * (N - 3)) := hmul
      _ = C₂ * (N ^ 3) := by
            simp [C₂]
            ring
  have hD_core :
      N ^ 2 * (N ^ 2 + 10 - 6 * N) ≤
        (N - 1) ^ 2 * (N - 2) ^ 2 := by
    apply Nat.le.intro (k := T)
    rw [hCinner, hT, hNm1, hNm2, hN]
    ring
  have hD_nat : C₃ * (N ^ 3) ≤ F * F := by
    have hmul := Nat.mul_le_mul_left (N ^ 2) hD_core
    calc
      C₃ * (N ^ 3) =
          N ^ 2 * (N ^ 2 * (N ^ 2 + 10 - 6 * N)) := by
            simp [C₃]
            ring
      _ ≤ N ^ 2 * ((N - 1) ^ 2 * (N - 2) ^ 2) := hmul
      _ = F * F := by
            simp [F]
            ring
  have hPpos : (0 : NNReal) < ((N ^ 3 : Nat) : NNReal) := by
    exact_mod_cast hP0
  have hF2pos : (0 : NNReal) < ((F * F : Nat) : NNReal) := by
    exact_mod_cast hF20
  have hA :
      1 / (((N ^ 3 : Nat) : NNReal)) ≤
        ((F : Nat) : NNReal) / (((F * F : Nat) : NNReal)) := by
    apply (div_le_div_iff₀ hPpos hF2pos).2
    norm_num
    exact_mod_cast hA_nat
  have hE :
      1 / (((N ^ 3 : Nat) : NNReal)) ≤
        ((C₂ : Nat) : NNReal) / (((F * F : Nat) : NNReal)) := by
    apply (div_le_div_iff₀ hPpos hF2pos).2
    norm_num
    exact_mod_cast hE_nat
  have hD :
      ((C₃ : Nat) : NNReal) / (((F * F : Nat) : NNReal)) ≤
        1 / (((N ^ 3 : Nat) : NNReal)) := by
    apply (div_le_div_iff₀ hF2pos hPpos).2
    norm_num
    exact_mod_cast hD_nat
  rw [hNm1, hNm2]
  rw [tsub_eq_zero_of_le hD, nsmul_zero, add_zero]
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_nsmul]
  rw [NNReal.coe_sub hA, NNReal.coe_sub hE]
  push_cast
  have hFk : F = (k + 5) * (k + 4) * (k + 3) := by
    dsimp [F]
    rw [hNm1, hNm2, hN]
  have hC₂k : C₂ = (k + 5) * (k + 3) * (k + 2) := by
    dsimp [C₂]
    rw [hNm2, hNm3, hN]
  rw [hFk, hC₂k, hT, hN]
  norm_num [nsmul_eq_mul]
  field_simp
  ring

end ExactThreeQueryCombinatorics

/-!
The combinatorial calculation is now transported back through the exact
law-level characterization.  These are the only public declarations in this
section.
-/

theorem sop_advantage_three_card_three (hG : Fintype.card G = 3) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 3) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) =
      (2 / 3 : ℝ) := by
  have hq : 3 ≤ Fintype.card G := by omega
  rw [RandomSystems.SoP.sop_advantage_eq_compatible_count_distance_of_le_card
    G 3 hq]
  simp_rw [compatible_count_eq_legacy G]
  change ((q3_positive_error (G := G) : NNReal) : ℝ) = 2 / 3
  rw [q3_positive_error_card_three hG]
  norm_num

theorem sop_advantage_three_card_four (hG : Fintype.card G = 4) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 3) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) =
      (5 / 48 : ℝ) := by
  have hq : 3 ≤ Fintype.card G := by omega
  rw [RandomSystems.SoP.sop_advantage_eq_compatible_count_distance_of_le_card
    G 3 hq]
  simp_rw [compatible_count_eq_legacy G]
  change ((q3_positive_error (G := G) : NNReal) : ℝ) = 5 / 48
  rw [q3_positive_error_card_four hG]
  norm_num

private theorem sop_advantage_three_card_ge_five
    (hG : 5 ≤ Fintype.card G) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 3) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) =
      (((((3 * Fintype.card G ^ 2 + 4 -
          12 * Fintype.card G : Nat) : NNReal) /
          ((Fintype.card G ^ 2 * (Fintype.card G - 1) *
            (Fintype.card G - 2) : Nat) : NNReal)) : NNReal) : ℝ) := by
  have hq : 3 ≤ Fintype.card G := by omega
  rw [RandomSystems.SoP.sop_advantage_eq_compatible_count_distance_of_le_card
    G 3 hq]
  simp_rw [compatible_count_eq_legacy G]
  change
    ((q3_positive_error (G := G) : NNReal) : ℝ) =
      (((((3 * Fintype.card G ^ 2 + 4 -
          12 * Fintype.card G : Nat) : NNReal) /
          ((Fintype.card G ^ 2 * (Fintype.card G - 1) *
            (Fintype.card G - 2) : Nat) : NNReal)) : NNReal) : ℝ)
  rw [q3_positive_error_card_ge_five hG]

theorem sop_advantage_three_card_ge_five_real
    (hG : 5 ≤ Fintype.card G) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 3) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) =
      (3 * (Fintype.card G : ℝ) ^ 2 -
          12 * (Fintype.card G : ℝ) + 4) /
        ((Fintype.card G : ℝ) ^ 2 *
          ((Fintype.card G : ℝ) - 1) *
          ((Fintype.card G : ℝ) - 2)) := by
  rw [sop_advantage_three_card_ge_five G hG]
  let N := Fintype.card G
  let k := N - 5
  have hN5 : 5 ≤ N := by simpa [N] using hG
  have hN : N = k + 5 := by omega
  have hNm1 : N - 1 = k + 4 := by omega
  have hNm2 : N - 2 = k + 3 := by omega
  have hnum :
      3 * N ^ 2 + 4 - 12 * N =
        3 * k ^ 2 + 18 * k + 19 := by
    rw [Nat.sub_eq_iff_eq_add]
    · rw [hN]
      ring
    · rw [hN]
      nlinarith
  change
    (((((3 * N ^ 2 + 4 - 12 * N : Nat) : NNReal) /
      ((N ^ 2 * (N - 1) * (N - 2) : Nat) : NNReal)) : NNReal) : ℝ) =
      (3 * (N : ℝ) ^ 2 - 12 * (N : ℝ) + 4) /
        ((N : ℝ) ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) - 2))
  rw [hnum, hNm1, hNm2, hN]
  push_cast
  norm_num
  congr 1 <;> ring

theorem sop_advantage_three_card_one (hG : Fintype.card G = 1) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 3) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) = 0 := by
  rw [RandomSystems.SoP.adv_prf_eq_visible_stat_dist_min_card G 3]
  have hmin : min 3 (Fintype.card G) = 1 := by omega
  rw [hmin]
  rw [← RandomSystems.SoP.adv_prf_eq_visible_stat_dist_of_le_card
    G 1 (by omega)]
  exact RandomSystems.SoP.sop_advantage_one G

theorem sop_advantage_three_card_two (hG : Fintype.card G = 2) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 3) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) =
      (1 / 2 : ℝ) := by
  rw [RandomSystems.SoP.adv_prf_eq_visible_stat_dist_min_card G 3]
  have hmin : min 3 (Fintype.card G) = 2 := by omega
  rw [hmin]
  rw [← RandomSystems.SoP.adv_prf_eq_visible_stat_dist_of_le_card
    G 2 (by omega)]
  rw [RandomSystems.SoP.sop_advantage_two G (by omega)]
  norm_num [hG]

/-!
### Saturation lower bound for abelian groups

At full-domain query depth a simple law-level test already gives a large
advantage.  The real table has a deterministic total sum, whereas the total
sum of a uniform function table is uniform.  We prove the latter by an
explicit equivalence which splits off the value at zero and translates that
coordinate by the sum of the remaining values.
-/

section AbelianSaturation

variable {A : Type*} [Fintype A] [AddCommGroup A]

/-- Total output sum of a complete function table. -/
private def function_total (f : A → A) : A :=
  ∑ x, f x

/-- The deterministic total taken by every literal permutation-sum table. -/
private def permutation_sum_total : A :=
  (∑ x : A, x) + ∑ x : A, x

/-- The literal sum of two permutations has the same complete-table total
for every sampled permutation pair. -/
private theorem function_total_xop
    (p : Equiv.Perm A × Equiv.Perm A) :
    function_total (xop_function A p) =
      permutation_sum_total (A := A) := by
  simp only [function_total, xop_function, permutation_sum_total,
    Finset.sum_add_distrib]
  congr 1
  · exact
      Fintype.sum_equiv p.1
        (fun x => p.1 x) (fun x => x) (fun _ => rfl)
  · exact
      Fintype.sum_equiv p.2
        (fun x => p.2 x) (fun x => x) (fun _ => rfl)

/-- Function values away from zero. -/
private abbrev function_tail (A : Type*) [Zero A] :=
  {x : A // x ≠ 0} → A

/-- Split a complete function into its value at zero and all remaining
values. -/
private def split_function :
    (A → A) ≃ A × function_tail A :=
  Equiv.piSplitAt 0 (fun _ => A)

/-- Translate the distinguished coordinate by the sum of the tail.  The
first projection after this equivalence is the total function sum. -/
private def add_tail_total_equiv :
    A × function_tail A ≃ A × function_tail A where
  toFun p := (p.1 + ∑ x, p.2 x, p.2)
  invFun p := (p.1 - ∑ x, p.2 x, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- The total sum factors through the two explicit equivalences above and a
first projection. -/
private theorem function_total_split (f : A → A) :
    function_total f =
      (add_tail_total_equiv
        (split_function f)).1 := by
  have h :=
    Fintype.sum_subtype_add_sum_subtype
      (fun x : A => x = 0) f
  simpa [function_total, add_tail_total_equiv,
    split_function] using h.symm

/-- The total of a uniform random function is uniform on the abelian
codomain. -/
private theorem function_total_uniform :
    Dist.fTransform (function_total (A := A))
        (Dist.uniform (A → A)) =
      Dist.uniform A := by
  calc
    Dist.fTransform (function_total (A := A))
        (Dist.uniform (A → A)) =
        Dist.fTransform Prod.fst
          (Dist.fTransform (add_tail_total_equiv (A := A))
            (Dist.fTransform (split_function (A := A))
              (Dist.uniform (A → A)))) := by
      rw [Dist.fTransform_comp, Dist.fTransform_comp]
      congr 1
      funext f
      exact function_total_split f
    _ = Dist.fTransform Prod.fst
          (Dist.fTransform (add_tail_total_equiv (A := A))
            (Dist.uniform (A × function_tail A))) := by
      rw [Dist.fTransform_equiv_uniform]
    _ = Dist.fTransform Prod.fst
          (Dist.uniform (A × function_tail A)) := by
      rw [Dist.fTransform_equiv_uniform]
    _ = Dist.uniform A :=
      Dist.fTransform_fst_uniform A (function_tail A)

/-- The real complete table passes the total-sum test with probability one. -/
private theorem real_function_total_mass :
    (real_function_law A).val.mass
        (fun f => function_total f =
          permutation_sum_total (A := A)) = 1 := by
  rw [real_function_law, Common.induced_function_law,
    Dist.mass_fTransform]
  rw [show
      (fun p : Equiv.Perm A × Equiv.Perm A =>
        function_total (xop_function A p) =
          permutation_sum_total (A := A)) =
        fun _ => True by
      funext p
      simp [function_total_xop]]
  rw [Dist.mass_true, Dist.weight_uniform]

/-- The ideal complete table passes any prescribed total-sum test with
probability exactly `1 / |A|`. -/
private theorem ideal_function_total_mass (c : A) :
    (ideal_function_law A).val.mass
        (fun f => function_total f = c) =
      1 / (Fintype.card A : NNReal) := by
  rw [ideal_function_law,
    Dist.mass_preimage_eq_fTransform_apply,
    function_total_uniform, Dist.uniform_apply]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one]

/-- Paper Proposition 11.  Once every input can be queried, the adaptive
advantage over a finite abelian group is at least `1 - 1/N`.  The theorem
surface contains only the concrete law-level systems and the numerical
bound; the total-sum event is confined to the proof. -/
theorem sop_abelian_saturation_lower_bound
    (q : Nat) (hq : Fintype.card A ≤ q) :
    1 - 1 / (Fintype.card A : ℝ) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop A) (urf A) := by
  rw [adv_prf_eq_full_function_distance_of_card_le A q hq]
  let P : (A → A) → Prop :=
    fun f =>
      function_total f = permutation_sum_total (A := A)
  calc
    1 - 1 / (Fintype.card A : ℝ) =
        ((real_function_law A).val.mass P : ℝ) -
          ((ideal_function_law A).val.mass P : ℝ) := by
      rw [real_function_total_mass,
        ideal_function_total_mass]
      norm_num
    _ ≤ (RandomSystems.statDist
          (real_function_law A).val
          (ideal_function_law A).val : ℝ) :=
      RandomSystems.mass_sub_mass_le_statDist
        (real_function_law A).val
        (ideal_function_law A).val P

end AbelianSaturation

/-!
## 5. Sequential cubic benchmark

### One-step law for the residual-free numerical bound

The numerical endpoint is proved by exposing fresh permutation images.  After
`r` successful fresh steps, the next two images are uniform on the complements
of the two used image sets.  The following local development computes the
literal-sum output law exactly.  It is introduced here because it is the
current proof obligation for the public security bound; none of these hidden
sets will occur in that theorem's statement.
-/

section SequentialOneStep

variable {H : Type*} [Fintype H] [AddGroup H]

/-!
#### Finite kernels used by the sequential joint

Paper Proposition 8 is a recursive joint probability law.  The repository's
finite distribution type has pushforwards and products but no kernel
composition operation, so we introduce exactly that operation here.  Its
normalization and pushforward laws are the two facts used below to prove the
marginals of the recursive coupling.
-/

/-- Composition of a finite probability law with a finite probability
kernel.  This is the finite sum
`(X >>= K)(b) = ∑ a, X(a) K(a)(b)`. -/
private noncomputable def finite_kernel_comp
    {A B : Type*} [Fintype A] [Fintype B]
    (X : Dist.ProbDist A) (K : A → Dist.ProbDist B) :
    Dist.ProbDist B :=
  ⟨Dist.ofFiniteMassFunction (fun b => ∑ a : A, X a * K a b), by
    rw [Dist.isProbDist]
    constructor
    · intro b
      rw [Dist.ofFiniteMassFunction_apply]
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (X.property.nonNeg a) ((K a).property.nonNeg b)
    · rw [Dist.weight_ofFiniteMassFunction]
      rw [Finset.sum_comm]
      calc
        (∑ a : A, ∑ b : B, X a * K a b) =
            ∑ a : A, X a * ∑ b : B, K a b := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
        _ = ∑ a : A, X a := by
              apply Finset.sum_congr rfl
              intro a _
              rw [← Dist.weight_eq_sum, (K a).property.weight_eq, mul_one]
        _ = 1 := by
              rw [← Dist.weight_eq_sum, X.property.weight_eq]⟩

@[simp]
private theorem finite_kernel_comp_apply
    {A B : Type*} [Fintype A] [Fintype B]
    (X : Dist.ProbDist A) (K : A → Dist.ProbDist B) (b : B) :
    finite_kernel_comp X K b = ∑ a : A, X a * K a b := by
  simp [finite_kernel_comp]

/-- Deterministic postprocessing commutes with finite kernel composition. -/
private theorem ftransform_finite_kernel_comp
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (X : Dist.ProbDist A) (K : A → Dist.ProbDist B) (f : B → C) :
    Dist.fTransform f (finite_kernel_comp X K).val =
      (finite_kernel_comp X
        (fun a => ⟨Dist.fTransform f (K a).val,
          Dist.fTransform_isProbDist f (K a).property⟩)).val := by
  apply Finsupp.ext
  intro c
  rw [finite_kernel_comp_apply, Dist.fTransform_apply_eq_sum]
  simp_rw [finite_kernel_comp_apply]
  simp only [Finset.sum_filter]
  calc
    (∑ b : B,
        if f b = c then ∑ a : A, X a * K a b else 0) =
        ∑ b : B, ∑ a : A,
          if f b = c then X a * K a b else 0 := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases h : f b = c <;> simp [h]
    _ = ∑ a : A, ∑ b : B,
          if f b = c then X a * K a b else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ a : A, X a * (Dist.fTransform f (K a).val) c := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Dist.fTransform_apply_eq_sum]
            simp only [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            by_cases h : f b = c <;> simp [h]

/-- Binding a probability law against a constant kernel returns that law. -/
private theorem finite_kernel_comp_const
    {A B : Type*} [Fintype A] [Fintype B]
    (X : Dist.ProbDist A) (Y : Dist.ProbDist B) :
    (finite_kernel_comp X (fun _ => Y)).val = Y.val := by
  apply Finsupp.ext
  intro b
  rw [finite_kernel_comp_apply, ← Finset.sum_mul,
    ← Dist.weight_eq_sum, X.property.weight_eq, one_mul]

/-- Event mass under kernel composition is the average of the conditional
event masses. -/
private theorem finite_kernel_comp_mass
    {A B : Type*} [Fintype A] [Fintype B]
    (X : Dist.ProbDist A) (K : A → Dist.ProbDist B)
    (P : B → Prop) :
    (finite_kernel_comp X K).val.mass P =
      ∑ a : A, X a * (K a).val.mass P := by
  rw [Dist.mass_eq_sum]
  simp_rw [finite_kernel_comp_apply]
  calc
    (∑ b : B, if P b then ∑ a : A, X a * K a b else 0) =
        ∑ b : B, ∑ a : A,
          if P b then X a * K a b else 0 := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases h : P b <;> simp [h]
    _ = ∑ a : A, ∑ b : B,
          if P b then X a * K a b else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ a : A, X a * (K a).val.mass P := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Dist.mass_eq_sum]
            simp only [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            by_cases h : P b <;> simp [h]

/-- Kernel composition depends on a state only through a deterministic
statistic exactly when it can be performed after pushing the state law to
that statistic. -/
private theorem finite_kernel_comp_factor
    {A B C : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Fintype C] [Nonempty C]
    (X : Dist.ProbDist A) (g : A → C)
    (L : C → Dist.ProbDist B) :
    (finite_kernel_comp X (fun a => L (g a))).val =
      (finite_kernel_comp
        ⟨Dist.fTransform g X.val,
          Dist.fTransform_isProbDist g X.property⟩ L).val := by
  apply Finsupp.ext
  intro b
  rw [finite_kernel_comp_apply, finite_kernel_comp_apply]
  exact
    (Dist.fTransform_sum_mul X.val g (fun c => L c b)).symm

/-- Sampling `a`, then `b`, then applying `f a b` is the pushforward of the
independent product law. -/
private theorem finite_kernel_comp_map_prod
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (X : Dist.ProbDist A) (Y : Dist.ProbDist B) (f : A → B → C) :
    (finite_kernel_comp X
      (fun a =>
        ⟨Dist.fTransform (f a) Y.val,
          Dist.fTransform_isProbDist (f a) Y.property⟩)).val =
      Dist.fTransform (fun p : A × B => f p.1 p.2)
        (Dist.prodProbDist X Y).val := by
  apply Finsupp.ext
  intro c
  rw [finite_kernel_comp_apply, Dist.fTransform_apply_eq_sum]
  simp_rw [Dist.fTransform_apply_eq_sum]
  simp only [Finset.sum_filter, Dist.prodProbDist_val]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Dist.prod_apply]
  by_cases h : f a b = c <;> simp [h]

/-- Image values already used by an injective tape prefix. -/
private def used_image {r : Nat} (a : Fin r ↪ H) : Finset H :=
  Finset.univ.image a

/-- Values outside a finite used-image set. -/
private abbrev unused (A : Finset H) : Type _ :=
  {x : H // x ∉ A}

/-- The pair of unused images available after the hidden prefixes `a,b`. -/
private abbrev available_pair {r : Nat} (a b : Fin r ↪ H) : Type _ :=
  unused (used_image a) × unused (used_image b)

/-- Literal sum revealed by an available hidden-image pair. -/
private def available_pair_sum {r : Nat} {a b : Fin r ↪ H}
    (u : available_pair a b) : H :=
  u.1.1 + u.2.1

/-- A strict-cardinality subset has a nonempty complement. -/
private theorem unused_nonempty (A : Finset H)
    (hA : A.card < Fintype.card H) :
    Nonempty (unused A) := by
  have hc : 0 < Aᶜ.card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hc
  exact ⟨⟨x, Finset.mem_compl.mp hx⟩⟩

/-- Conditional law of the next literal-sum output after two injective image
prefixes have been exposed. -/
private noncomputable def real_next_output {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist.ProbDist H := by
  let A := used_image a
  let B := used_image b
  have hAcard : A.card = r := by
    simp [A, used_image, Finset.card_image_of_injective, a.injective]
  have hBcard : B.card = r := by
    simp [B, used_image, Finset.card_image_of_injective, b.injective]
  letI : Nonempty (unused A) :=
    unused_nonempty A (hAcard ▸ hr)
  letI : Nonempty (unused B) :=
    unused_nonempty B (hBcard ▸ hr)
  exact
    ⟨Dist.fTransform
        (fun p : unused A × unused B => p.1.1 + p.2.1)
        (Dist.uniform (unused A × unused B)),
      Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Number of already-used image pairs whose literal sum is `z`. -/
private def cross_count {r : Nat}
    (a b : Fin r ↪ H) (z : H) : Nat :=
  ((used_image a).filter
    (fun x => -x + z ∈ used_image b)).card

/-- Number of currently unused image pairs whose literal sum is `z`, written
using the first image as the free coordinate. -/
private def unused_sum_count {r : Nat}
    (a b : Fin r ↪ H) (z : H) : Nat :=
  (((Finset.univ : Finset H) \ used_image a).filter
    (fun x => -x + z ∉ used_image b)).card

private theorem used_image_card {r : Nat} (a : Fin r ↪ H) :
    (used_image a).card = r := by
  simp [used_image, Finset.card_image_of_injective, a.injective]

/-- Translation-inversion is a bijection, so the preimage of either used set
has the same cardinality `r`. -/
private theorem translate_preimage_card {r : Nat}
    (b : Fin r ↪ H) (z : H) :
    ((Finset.univ : Finset H).filter
      (fun x => -x + z ∈ used_image b)).card = r := by
  let e : H ≃ H :=
    { toFun := fun x => -x + z
      invFun := fun y => z - y
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  calc
    ((Finset.univ : Finset H).filter
        (fun x => -x + z ∈ used_image b)).card =
        (Finset.univ.filter
          (fun x => e x ∈ used_image b)).card := rfl
    _ = (used_image b).card := by
      apply Finset.card_bij (fun x _ => e x)
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x hx y hy hxy
        exact e.injective hxy
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa using hy⟩
    _ = r := used_image_card b

/-- Inclusion-exclusion form of the available-pair count:
`N - 2r + c_z`.  Integers make all subtraction side conditions explicit. -/
private theorem unused_sum_count_int {r : Nat}
    (a b : Fin r ↪ H) (z : H) :
    (unused_sum_count a b z : Int) =
      Fintype.card H - 2 * r + cross_count a b z := by
  let A := used_image a
  let T := (Finset.univ : Finset H).filter
    (fun x => -x + z ∈ used_image b)
  have hA : A.card = r := used_image_card a
  have hT : T.card = r := translate_preimage_card b z
  have hc : (A ∩ T).card = cross_count a b z := by
    simp only [A, T, cross_count]
    congr 1
    ext x
    simp
  have hu :
      (A ∪ T).card + (A ∩ T).card = A.card + T.card :=
    Finset.card_union_add_card_inter A T
  have hcomp :
      ((A ∪ T)ᶜ).card =
        Fintype.card H - (A ∪ T).card := by
    rw [Finset.card_compl]
  have hUle : (A ∪ T).card ≤ Fintype.card H := by
    simpa using
      Finset.card_le_card (Finset.subset_univ (A ∪ T))
  have heq :
      unused_sum_count a b z = ((A ∪ T)ᶜ).card := by
    unfold unused_sum_count
    apply congrArg Finset.card
    ext x
    simp [A, T]
  rw [heq, hcomp]
  omega

private theorem unused_card {r : Nat} (a : Fin r ↪ H) :
    Fintype.card (unused (used_image a)) =
      Fintype.card H - r := by
  rw [Fintype.card_subtype_compl
    (p := fun x : H => x ∈ used_image a)]
  congr 1
  simpa using used_image_card a

/-- The available-pair fiber over `z` is counted by `unused_sum_count`. -/
private theorem unused_pair_fiber_card {r : Nat}
    (a b : Fin r ↪ H) (z : H) :
    ((Finset.univ : Finset
      (unused (used_image a) × unused (used_image b))).filter
        (fun p => p.1.1 + p.2.1 = z)).card =
      unused_sum_count a b z := by
  apply Finset.card_bij (fun p _ => p.1.1)
  · intro p hp
    rw [Finset.mem_filter]
    refine
      ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, p.1.2⟩, ?_⟩
    intro hmem
    apply p.2.2
    have hout := (Finset.mem_filter.mp hp).2
    have hsecond : p.2.1 = -p.1.1 + z :=
      eq_neg_add_iff_add_eq.mpr hout
    simpa [hsecond] using hmem
  · intro p hp q hq hpq
    apply Prod.ext
    · exact Subtype.ext hpq
    · apply Subtype.ext
      have hpout := (Finset.mem_filter.mp hp).2
      have hqout := (Finset.mem_filter.mp hq).2
      have hpsecond : p.2.1 = -p.1.1 + z :=
        eq_neg_add_iff_add_eq.mpr hpout
      have hqsecond : q.2.1 = -q.1.1 + z :=
        eq_neg_add_iff_add_eq.mpr hqout
      exact hpsecond.trans
        ((congrArg (fun x : H => -x + z) hpq).trans
          hqsecond.symm)
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    refine
      ⟨(⟨x, (Finset.mem_sdiff.mp hx'.1).2⟩,
        ⟨-x + z, hx'.2⟩), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simp⟩
    · rfl

/-- The output fiber containing an available pair is nonempty.  This is the
denominator side condition in the hidden-pair lift of Proposition 8. -/
private theorem unused_sum_count_pos_of_pair {r : Nat}
    (a b : Fin r ↪ H) (u : available_pair a b) :
    0 < unused_sum_count a b (available_pair_sum u) := by
  rw [← unused_pair_fiber_card]
  exact Finset.card_pos.mpr
    ⟨u, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, rfl⟩⟩

/-- Exact conditional point mass of the next real output. -/
private theorem real_next_output_apply {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) (z : H) :
    (real_next_output hr a b).val z =
      (unused_sum_count a b z : NNReal) /
        (((Fintype.card H - r) *
          (Fintype.card H - r) : Nat) : NNReal) := by
  letI : Nonempty (unused (used_image a)) :=
    unused_nonempty _ (by
      rw [used_image_card]
      exact hr)
  letI : Nonempty (unused (used_image b)) :=
    unused_nonempty _ (by
      rw [used_image_card]
      exact hr)
  unfold real_next_output
  dsimp only
  rw [Dist.fTransform_apply_eq_mass,
    Dist.uniform_mass_eq_card_filter]
  rw [unused_pair_fiber_card, Fintype.card_prod,
    unused_card, unused_card]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

/-- Every used-pair sum fiber is contained in the first used image set. -/
private theorem cross_count_le {r : Nat}
    (a b : Fin r ↪ H) (z : H) :
    cross_count a b z ≤ r := by
  calc
    cross_count a b z ≤ (used_image a).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = r := used_image_card a

/-- The used-pair fiber over `z` is counted by `cross_count`. -/
private theorem used_pair_fiber_card {r : Nat}
    (a b : Fin r ↪ H) (z : H) :
    (((used_image a).product (used_image b)).filter
      (fun p => p.1 + p.2 = z)).card =
      cross_count a b z := by
  unfold cross_count
  apply Finset.card_bij
    (s := ((used_image a).product (used_image b)).filter
      (fun p => p.1 + p.2 = z))
    (fun p _ => p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpmem := Finset.mem_product.mp hp'.1
    exact Finset.mem_filter.mpr
      ⟨hpmem.1, by
        have hout := hp'.2
        have hsecond : p.2 = -p.1 + z :=
          eq_neg_add_iff_add_eq.mpr hout
        simpa [hsecond] using hpmem.2⟩
  · intro p hp q hq hpq
    apply Prod.ext hpq
    have hpout := (Finset.mem_filter.mp hp).2
    have hqout := (Finset.mem_filter.mp hq).2
    have hpsecond : p.2 = -p.1 + z :=
      eq_neg_add_iff_add_eq.mpr hpout
    have hqsecond : q.2 = -q.1 + z :=
      eq_neg_add_iff_add_eq.mpr hqout
    exact hpsecond.trans
      ((congrArg (fun x : H => -x + z) hpq).trans
        hqsecond.symm)
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    refine ⟨(x, -x + z), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx'.1, hx'.2⟩, by simp⟩

/-- The collision multiplicities partition the `r²` used image pairs. -/
private theorem sum_cross_count {r : Nat}
    (a b : Fin r ↪ H) :
    ∑ z : H, cross_count a b z = r * r := by
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise
      (s := (used_image a).product (used_image b))
      (t := (Finset.univ : Finset H))
      (f := fun p : H × H => p.1 + p.2)
      (fun _ _ => Finset.mem_univ _)
  change
    ((used_image a) ×ˢ (used_image b)).card = _ at hpartition
  rw [Finset.card_product, used_image_card,
    used_image_card] at hpartition
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro z _
  exact (used_pair_fiber_card a b z).symm

/-- Pointwise positive excess over uniform is charged to the corresponding
used-pair multiplicity. -/
private theorem real_next_output_tsub_uniform_le {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) (z : H) :
    (real_next_output hr a b).val z - Dist.uniform H z ≤
      (cross_count a b z : NNReal) /
        (((Fintype.card H) *
          (Fintype.card H - r) : Nat) : NNReal) := by
  rw [real_next_output_apply, Dist.uniform_apply,
    tsub_le_iff_right]
  have hN : (Fintype.card H : NNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := H)).ne'
  have hNr :
      ((Fintype.card H - r : Nat) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hr).ne'
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_one, Nat.cast_mul]
  rw [Nat.cast_sub (Nat.le_of_lt hr)]
  have hNreal : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := H)).ne'
  have hNrreal :
      (Fintype.card H : ℝ) - r ≠ 0 := by
    exact sub_ne_zero.mpr (by
      exact_mod_cast (ne_of_gt hr))
  have hNpos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := H)
  have hNrpos :
      0 < (Fintype.card H : ℝ) - r := by
    exact sub_pos.mpr (by exact_mod_cast hr)
  have hrhs :
      (cross_count a b z : ℝ) /
          ((Fintype.card H : ℝ) *
            ((Fintype.card H : ℝ) - r)) +
        1 / (Fintype.card H : ℝ) =
      ((cross_count a b z : ℝ) +
          ((Fintype.card H : ℝ) - r)) /
        ((Fintype.card H : ℝ) *
          ((Fintype.card H : ℝ) - r)) := by
    field_simp [hNreal, hNrreal]
  rw [hrhs]
  apply
    (div_le_div_iff₀
      (mul_pos hNrpos hNrpos)
      (mul_pos hNpos hNrpos)).2
  have hc := cross_count_le a b z
  have hcount := unused_sum_count_int a b z
  have hcR :
      (cross_count a b z : ℝ) ≤ r := by
    exact_mod_cast hc
  have hcountR :
      (unused_sum_count a b z : ℝ) =
        Fintype.card H - 2 * r + cross_count a b z := by
    exact_mod_cast hcount
  have hcore :
      (unused_sum_count a b z : ℝ) *
          (Fintype.card H : ℝ) ≤
        ((cross_count a b z : ℝ) +
          ((Fintype.card H : ℝ) - r)) *
          ((Fintype.card H : ℝ) - r) := by
    rw [hcountR]
    nlinarith
  calc
    (unused_sum_count a b z : ℝ) *
        ((Fintype.card H : ℝ) *
          ((Fintype.card H : ℝ) - r)) =
        ((unused_sum_count a b z : ℝ) *
          (Fintype.card H : ℝ)) *
            ((Fintype.card H : ℝ) - r) := by ring
    _ ≤ (((cross_count a b z : ℝ) +
          ((Fintype.card H : ℝ) - r)) *
            ((Fintype.card H : ℝ) - r)) *
          ((Fintype.card H : ℝ) - r) :=
      mul_le_mul_of_nonneg_right hcore hNrpos.le
    _ = ((cross_count a b z : ℝ) +
          ((Fintype.card H : ℝ) - r)) *
        (((Fintype.card H : ℝ) - r) *
          ((Fintype.card H : ℝ) - r)) := by ring

/-- The exact conditional real law is within
`r² / (N(N-r))` of uniform. -/
private theorem real_next_output_distance_le {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    RandomSystems.statDist
        (real_next_output hr a b).val (Dist.uniform H) ≤
      ((r * r : Nat) : NNReal) /
        (((Fintype.card H) *
          (Fintype.card H - r) : Nat) : NNReal) := by
  unfold RandomSystems.statDist
  calc
    (∑ z : H,
        max ((real_next_output hr a b).val z -
          Dist.uniform H z) 0) ≤
        ∑ z : H,
          (cross_count a b z : Real) /
            (((Fintype.card H) *
              (Fintype.card H - r) : Nat) : Real) :=
      Finset.sum_le_sum (fun z _ => max_le
        (real_next_output_tsub_uniform_le hr a b z)
        (by positivity))
    _ = (((((r * r : Nat) : NNReal) /
          (((Fintype.card H) *
            (Fintype.card H - r) : Nat) : NNReal)) : NNReal) : Real) := by
      simp only [NNReal.coe_div, NNReal.coe_natCast]
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast sum_cross_count a b

/-!
#### The one-step joint and its hidden-pair lift

Lemma 7 only bounds a distance.  Proposition 8 additionally needs a joint
law.  We maximally couple the real next-output law with uniform, then
disintegrate its real output uniformly over the corresponding unused-pair
fiber.  The next four declarations prove normalization, both marginals, and
that the actual hidden/output disagreement is exactly the disagreement of the
maximal output coupling.
-/

private theorem ftransform_fst_pair_apply
    {A B : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (a : A) :
    (Dist.fTransform Prod.fst D) a = ∑ b : B, D (a, b) := by
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  trans
    (∑ p ∈ (Finset.univ : Finset (A × B)),
      if p.1 = a then D p else 0)
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp
  · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs =>
      rw [show (∑ b : B, D (a, b)) =
          ∑ p ∈ (Finset.univ : Finset B).map
              ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩,
            D p from by rw [Finset.sum_map]; simp]
    congr 1
    ext ⟨x, y⟩
    simp [eq_comm]

private theorem ftransform_snd_pair_apply
    {A B : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (b : B) :
    (Dist.fTransform Prod.snd D) b = ∑ a : A, D (a, b) := by
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  trans
    (∑ p ∈ (Finset.univ : Finset (A × B)),
      if p.2 = b then D p else 0)
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp
  · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs =>
      rw [show (∑ a : A, D (a, b)) =
          ∑ p ∈ (Finset.univ : Finset A).map
              ⟨fun a => (a, b), fun a₁ a₂ h => by simpa using h⟩,
            D p from by rw [Finset.sum_map]; simp]
    congr 1
    ext ⟨x, y⟩
    simp [eq_comm]

private theorem ftransform_map_fst_pair_apply
    {A B C : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (f : A → C) (c : C) (b : B) :
    (Dist.fTransform (fun p : A × B => (f p.1, p.2)) D) (c, b) =
      ∑ a ∈ (Finset.univ : Finset A).filter (fun a => f a = c),
        D (a, b) := by
  rw [Dist.fTransform_apply_eq_sum]
  have hfilter :
      (Finset.univ.filter
          (fun p : A × B => (f p.1, p.2) = (c, b))) =
        ((Finset.univ : Finset A).filter (fun a => f a = c)).product {b} := by
    ext p
    rcases p with ⟨a, b'⟩
    simp [Prod.ext_iff, eq_comm]
  rw [hfilter]
  calc
    ∑ p ∈
        ((Finset.univ : Finset A).filter (fun a => f a = c)).product {b},
        D p =
        ∑ a ∈ (Finset.univ : Finset A).filter (fun a => f a = c),
          ∑ b' ∈ ({b} : Finset B), D (a, b') :=
      Finset.sum_product _ _ _
    _ = _ := by simp

/-- A chosen maximal coupling of the two one-step output laws. -/
private noncomputable def next_output_coupling {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    DistCoupling (real_next_output hr a b).val (Dist.uniform H) :=
  Classical.choose
    (RandomSystems.optimal_coupling_exists
      (real_next_output hr a b).property.nonNeg
      Dist.uniform_nonNeg
      ((real_next_output hr a b).property.weight_eq.trans
        Dist.weight_uniform.symm))

private theorem next_output_coupling_disagreement {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    (next_output_coupling hr a b).prDisagree =
      RandomSystems.statDist
        (real_next_output hr a b).val (Dist.uniform H) :=
  (Classical.choose_spec
    (RandomSystems.optimal_coupling_exists
      (real_next_output hr a b).property.nonNeg
      Dist.uniform_nonNeg
      ((real_next_output hr a b).property.weight_eq.trans
        Dist.weight_uniform.symm))).symm

/-- Honest uniform choice of the unused image pair. -/
private noncomputable def available_pair_uniform {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist.ProbDist (available_pair a b) := by
  letI : Nonempty (unused (used_image a)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  letI : Nonempty (unused (used_image b)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  exact ⟨Dist.uniform (available_pair a b), Dist.uniform_isProbDist⟩

/-- Lift the maximal output coupling by choosing the real unused pair
uniformly in the fiber of its output. -/
private noncomputable def coupled_fresh_step_dist {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist (available_pair a b × H) :=
  Dist.ofFiniteMassFunction fun w =>
    (next_output_coupling hr a b).joint
        (available_pair_sum w.1, w.2) /
      (unused_sum_count a b (available_pair_sum w.1) : NNReal)

@[simp]
private theorem coupled_fresh_step_dist_apply {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H)
    (u : available_pair a b) (z : H) :
    coupled_fresh_step_dist hr a b (u, z) =
      (next_output_coupling hr a b).joint
          (available_pair_sum u, z) /
        (unused_sum_count a b (available_pair_sum u) : NNReal) := by
  simp [coupled_fresh_step_dist]

/-- First marginal audit for the hidden-pair lift. -/
private theorem coupled_fresh_step_fst {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist.fTransform Prod.fst (coupled_fresh_step_dist hr a b) =
      (available_pair_uniform hr a b).val := by
  letI : Nonempty (unused (used_image a)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  letI : Nonempty (unused (used_image b)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  change
    Dist.fTransform Prod.fst (coupled_fresh_step_dist hr a b) =
      Dist.uniform (available_pair a b)
  apply Finsupp.ext
  intro u
  rw [ftransform_fst_pair_apply]
  simp_rw [coupled_fresh_step_dist_apply]
  rw [← Finset.sum_div,
    ← ftransform_fst_pair_apply,
    (next_output_coupling hr a b).marginal_fst,
    real_next_output_apply,
    Dist.uniform_apply,
    Fintype.card_prod, unused_card, unused_card]
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  have hc :
      (unused_sum_count a b (available_pair_sum u) : Real) ≠ 0 := by
    exact_mod_cast
      (unused_sum_count_pos_of_pair a b u).ne'
  field_simp [hc]

/-- Pushing the lift to `(real output, ideal output)` recovers exactly the
chosen maximal output coupling. -/
private theorem coupled_fresh_step_output_joint {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist.fTransform
        (fun w : available_pair a b × H =>
          (available_pair_sum w.1, w.2))
        (coupled_fresh_step_dist hr a b) =
      (next_output_coupling hr a b).joint := by
  apply Finsupp.ext
  rintro ⟨y, z⟩
  rw [ftransform_map_fst_pair_apply]
  let fiber :=
    (Finset.univ : Finset (available_pair a b)).filter
      (fun u => available_pair_sum u = y)
  by_cases hnonempty : fiber.Nonempty
  · have hcard_ne : ((fiber.card : Nat) : NNReal) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hnonempty).ne'
    calc
      ∑ u ∈ (Finset.univ : Finset (available_pair a b)).filter
          (fun u => available_pair_sum u = y),
          coupled_fresh_step_dist hr a b (u, z) =
          ∑ _u ∈ fiber,
            (next_output_coupling hr a b).joint (y, z) /
              (fiber.card : NNReal) := by
            apply Finset.sum_congr rfl
            intro u hu
            have huy : available_pair_sum u = y :=
              (Finset.mem_filter.mp hu).2
            rw [coupled_fresh_step_dist_apply, huy]
            congr 1
            exact_mod_cast
              (unused_pair_fiber_card a b y).symm
      _ = (fiber.card : NNReal) *
            ((next_output_coupling hr a b).joint (y, z) /
              (fiber.card : NNReal)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (next_output_coupling hr a b).joint (y, z) := by
            field_simp [hcard_ne]
  · have hempty : fiber = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hreal_zero :
        (real_next_output hr a b).val y = 0 := by
      rw [real_next_output_apply]
      have hcount :
          unused_sum_count a b y = 0 := by
        rw [← unused_pair_fiber_card]
        exact Finset.card_eq_zero.mpr hempty
      simp [hcount]
    have hleft_zero :
        (Dist.fTransform Prod.fst
          (next_output_coupling hr a b).joint) y = 0 := by
      rw [(next_output_coupling hr a b).marginal_fst,
        hreal_zero]
    rw [ftransform_fst_pair_apply] at hleft_zero
    have hjoint_zero :
        (next_output_coupling hr a b).joint (y, z) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => (next_output_coupling hr a b).nonneg (y, z))).mp
          hleft_zero z (Finset.mem_univ z)
    simpa [fiber, hempty, hjoint_zero]

/-- Second marginal audit for the hidden-pair lift. -/
private theorem coupled_fresh_step_snd {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist.fTransform Prod.snd (coupled_fresh_step_dist hr a b) =
      Dist.uniform H := by
  calc
    Dist.fTransform Prod.snd (coupled_fresh_step_dist hr a b) =
        Dist.fTransform Prod.snd
          (Dist.fTransform
            (fun w : available_pair a b × H =>
              (available_pair_sum w.1, w.2))
            (coupled_fresh_step_dist hr a b)) := by
          rw [Dist.fTransform_comp]
          rfl
    _ = Dist.fTransform Prod.snd
          (next_output_coupling hr a b).joint := by
          rw [coupled_fresh_step_output_joint]
    _ = Dist.uniform H :=
      (next_output_coupling hr a b).marginal_snd

/-- The lifted one-step law is normalized. -/
private theorem coupled_fresh_step_is_prob_dist {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    (coupled_fresh_step_dist hr a b).isProbDist := by
  constructor
  · intro w
    rcases w with ⟨u, z⟩
    rw [coupled_fresh_step_dist_apply]
    exact div_nonneg
      ((next_output_coupling hr a b).nonneg _)
      (by positivity)
  · calc
      (coupled_fresh_step_dist hr a b).weight =
          (Dist.fTransform Prod.fst
            (coupled_fresh_step_dist hr a b)).weight :=
        (Dist.weight_fTransform Prod.fst
          (coupled_fresh_step_dist hr a b)).symm
      _ = (available_pair_uniform hr a b).val.weight := by
        rw [coupled_fresh_step_fst]
      _ = 1 := (available_pair_uniform hr a b).property.weight_eq

private noncomputable def coupled_fresh_step {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    Dist.ProbDist (available_pair a b × H) :=
  ⟨coupled_fresh_step_dist hr a b,
    coupled_fresh_step_is_prob_dist hr a b⟩

/-- The event actually used by the sequential construction has exactly the
maximal output-coupling disagreement probability. -/
private theorem coupled_fresh_step_disagreement {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    (coupled_fresh_step hr a b).val.mass
        (fun w => available_pair_sum w.1 ≠ w.2) =
      RandomSystems.statDist
        (real_next_output hr a b).val (Dist.uniform H) := by
  rw [← next_output_coupling_disagreement hr a b]
  have hmass :
      (next_output_coupling hr a b).joint.mass
          (fun p => p.1 ≠ p.2) =
        (coupled_fresh_step hr a b).val.mass
          (fun w => available_pair_sum w.1 ≠ w.2) := by
    rw [← coupled_fresh_step_output_joint hr a b,
      Dist.mass_fTransform]
    rfl
  rw [← hmass]
  rw [Dist.mass_eq_sum, DistCoupling.prDisagree,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.1 ≠ p.2 <;> simp [h]

/-!
The sequential construction needs one further honest marginal.  A uniform
permutation restricted to `r` distinct inputs is a uniform embedding
`Fin r ↪ H`; hence two independent restrictions form a uniform pair of
embeddings.  The following local law records their literal sums.  The
cardinality bridge is proved explicitly because it is also the normalization
check connecting this hidden-prefix presentation to the compatible-count
presentation used by the maximal tape coupling.
-/

/-- Number of pairs of injective image prefixes with a prescribed literal
sum tape. -/
private def literal_pair_count {r : Nat} (y : Fin r → H) : Nat :=
  ((Finset.univ :
      Finset ((Fin r ↪ H) × (Fin r ↪ H))).filter
    (fun p => ∀ i, p.1 i + p.2 i = y i)).card

/-- Negating the first image prefix bijects literal-sum fibers with the
normalized compatible fibers counted earlier. -/
private theorem literal_pair_count_eq_compatible_count {r : Nat}
    (y : Fin r → H) :
    literal_pair_count y = compatible_count H y := by
  unfold literal_pair_count compatible_count
  apply Finset.card_bij
    (fun p _ => fun i => -p.1 i)
  · intro p hp
    have hout := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        ⟨fun i j hij =>
            p.1.injective (neg_injective hij),
          fun i j hij =>
            p.2.injective (by
              simpa [eq_neg_add_iff_add_eq.mpr (hout i),
                eq_neg_add_iff_add_eq.mpr (hout j)] using hij)⟩⟩
  · intro p hp q hq hpq
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact neg_injective (congrFun hpq i)
    · apply Function.Embedding.ext
      intro i
      have hpout := (Finset.mem_filter.mp hp).2 i
      have hqout := (Finset.mem_filter.mp hq).2 i
      have hp2 : p.2 i = -p.1 i + y i :=
        eq_neg_add_iff_add_eq.mpr hpout
      have hq2 : q.2 i = -q.1 i + y i :=
        eq_neg_add_iff_add_eq.mpr hqout
      rw [hp2, hq2, congrFun hpq i]
  · intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    let p1 : Fin r ↪ H :=
      ⟨fun i => -a i,
        fun i j hij => ha'.1 (neg_injective hij)⟩
    let p2 : Fin r ↪ H :=
      ⟨fun i => a i + y i, ha'.2⟩
    refine ⟨(p1, p2), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun i => by simp [p1, p2]⟩
    · funext i
      simp [p1]

/-- Literal sums of two independent uniform injective image prefixes. -/
private noncomputable def real_prefix_tape {r : Nat}
    (hr : r ≤ Fintype.card H) :
    Dist.ProbDist (Fin r → H) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  exact
    ⟨Dist.fTransform
        (fun p : (Fin r ↪ H) × (Fin r ↪ H) =>
          fun i => p.1 i + p.2 i)
        (Dist.uniform ((Fin r ↪ H) × (Fin r ↪ H))),
      Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Exact point mass of the honest injective-prefix sum law. -/
private theorem real_prefix_tape_apply {r : Nat}
    (hr : r ≤ Fintype.card H) (y : Fin r → H) :
    (real_prefix_tape hr).val y =
      (compatible_count H y : NNReal) /
        (((Fintype.card H).descFactorial r *
          (Fintype.card H).descFactorial r : Nat) : NNReal) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  unfold real_prefix_tape
  dsimp only
  rw [Dist.fTransform_apply_eq_mass,
    Dist.uniform_mass_eq_card_filter]
  rw [Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fin]
  have hfilter :
      ((Finset.univ :
          Finset ((Fin r ↪ H) × (Fin r ↪ H))).filter
        (fun p => (fun i => p.1 i + p.2 i) = y)) =
      (Finset.univ.filter
        (fun p => ∀ i, p.1 i + p.2 i = y i)) := by
    ext p
    simp [funext_iff]
  rw [hfilter]
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  change
    (literal_pair_count y : Real) / _ = _
  rw [literal_pair_count_eq_compatible_count]

/-- The independent uniform law of the two injective image prefixes. -/
private noncomputable def prefix_embedding_pair_law {r : Nat}
    (hr : r ≤ Fintype.card H) :
    Dist.ProbDist ((Fin r ↪ H) × (Fin r ↪ H)) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  exact
    ⟨Dist.uniform ((Fin r ↪ H) × (Fin r ↪ H)),
      Dist.uniform_isProbDist⟩

/-- Point mass of the two-prefix hidden-state law. -/
private theorem prefix_embedding_pair_law_apply {r : Nat}
    (hr : r ≤ Fintype.card H)
    (p : (Fin r ↪ H) × (Fin r ↪ H)) :
    (prefix_embedding_pair_law hr).val p =
      1 /
        (((Fintype.card H).descFactorial r *
          (Fintype.card H).descFactorial r : Nat) : NNReal) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  unfold prefix_embedding_pair_law
  dsimp only
  rw [Dist.uniform_apply, Fintype.card_prod,
    Fintype.card_embedding_eq, Fintype.card_fin]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

/-- A prefix embedding together with one fresh terminal image. -/
private abbrev embedding_extension_sample (r : Nat) :=
  {p : (Fin r ↪ H) × H // p.2 ∉ used_image p.1}

/-- Append the fresh terminal image to an injective prefix. -/
private def embedding_extension_snoc {r : Nat}
    (s : embedding_extension_sample (H := H) r) :
    Fin (r + 1) ↪ H :=
  Fin.Embedding.snoc s.1.1 (by
    intro h
    apply s.2
    rcases h with ⟨i, hi⟩
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, hi⟩)

/-- Split an injective `(r+1)`-prefix into its first `r` images and fresh
terminal image. -/
private def embedding_extension_init {r : Nat}
    (e : Fin (r + 1) ↪ H) :
    embedding_extension_sample (H := H) r :=
  ⟨(Fin.Embedding.init e, e (Fin.last r)), by
    intro hmem
    rw [used_image, Finset.mem_image] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    have heq :
        e i.castSucc = e (Fin.last r) := hi
    exact
      Fin.ne_of_lt i.castSucc_lt_last
        (e.injective heq)⟩

/-- Uniform injective extensions are exactly uniform `(r+1)`-embeddings. -/
private def embedding_extension_equiv (r : Nat) :
    embedding_extension_sample (H := H) r ≃
      (Fin (r + 1) ↪ H) where
  toFun := embedding_extension_snoc
  invFun := embedding_extension_init
  left_inv := by
    intro s
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.Embedding.init_snoc _ _
    · exact Fin.Embedding.snoc_last
  right_inv := by
    intro e
    apply Function.Embedding.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.Embedding.snoc_last
    · exact Fin.Embedding.snoc_castSucc

/-- Attach a terminal answer to an output prefix. -/
private def snoc_tape {r : Nat} :
    (Fin r → H) × H → (Fin (r + 1) → H) :=
  fun p => Fin.snoc p.1 p.2

/-- The prefix sum law is the visible pushforward of its explicit hidden
embedding-pair law. -/
private theorem real_prefix_tape_eq_pair_pushforward {r : Nat}
    (hr : r ≤ Fintype.card H) :
    (real_prefix_tape hr).val =
      Dist.fTransform
        (fun p : (Fin r ↪ H) × (Fin r ↪ H) =>
          fun i => p.1 i + p.2 i)
        (prefix_embedding_pair_law hr).val := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le
      (by simpa using hr)
  rfl

/-- Appending a terminal coordinate is an equivalence of finite tape
presentations. -/
private def snoc_tape_equiv (r : Nat) :
    ((Fin r → H) × H) ≃ (Fin (r + 1) → H) :=
  (Equiv.prodComm _ _).trans
    (Fin.snocEquiv (fun _ : Fin (r + 1) => H))

/-- A uniform prefix followed by a uniform terminal coordinate is a uniform
extended tape. -/
private theorem snoc_uniform_tape (r : Nat) :
    Dist.fTransform snoc_tape
        (Dist.prod
          (Dist.uniform (Fin r → H))
          (Dist.uniform H)) =
      Dist.uniform (Fin (r + 1) → H) := by
  rw [Dist.prod_uniform]
  change
    Dist.fTransform (snoc_tape_equiv (H := H) r)
        (Dist.uniform ((Fin r → H) × H)) =
      Dist.uniform (Fin (r + 1) → H)
  exact Dist.fTransform_equiv_uniform _

/-!
### The recursive online joint

The state records both honest hidden injection prefixes and the ideal visible
tape.  At an agreeing state the next unused pair and ideal output are sampled
from `coupled_fresh_step`; after disagreement they are sampled independently.
Both branches have the same honest marginals.  This makes disagreement
absorbing without ever changing either oracle's law.
-/

private abbrev hidden_prefix (r : Nat) :=
  (Fin r ↪ H) × (Fin r ↪ H)

/-- Uniform law of one injective image prefix. -/
private noncomputable def prefix_embedding_law {r : Nat}
    (hr : r ≤ Fintype.card H) :
    Dist.ProbDist (Fin r ↪ H) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  exact ⟨Dist.uniform (Fin r ↪ H), Dist.uniform_isProbDist⟩

/-- Uniform choice of one unused image. -/
private noncomputable def unused_image_uniform {r : Nat}
    (hr : r < Fintype.card H) (a : Fin r ↪ H) :
    Dist.ProbDist (unused (used_image a)) := by
  letI : Nonempty (unused (used_image a)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  exact ⟨Dist.uniform (unused (used_image a)), Dist.uniform_isProbDist⟩

private def extend_one_embedding {r : Nat} (a : Fin r ↪ H)
    (u : unused (used_image a)) : Fin (r + 1) ↪ H :=
  embedding_extension_snoc ⟨(a, u.1), u.2⟩

/-- Honest transition kernel for one permutation-image prefix. -/
private noncomputable def embedding_extension_kernel {r : Nat}
    (hr : r < Fintype.card H) (a : Fin r ↪ H) :
    Dist.ProbDist (Fin (r + 1) ↪ H) :=
  ⟨Dist.fTransform (extend_one_embedding a)
      (unused_image_uniform hr a).val,
    Dist.fTransform_isProbDist _ (unused_image_uniform hr a).property⟩

private theorem prefix_embedding_law_apply {r : Nat}
    (hr : r ≤ Fintype.card H) (a : Fin r ↪ H) :
    prefix_embedding_law hr a =
      1 / ((Fintype.card H).descFactorial r : NNReal) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  change Dist.uniform (Fin r ↪ H) a = _
  rw [Dist.uniform_apply, Fintype.card_embedding_eq,
    Fintype.card_fin]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

private theorem unused_image_uniform_apply {r : Nat}
    (hr : r < Fintype.card H) (a : Fin r ↪ H)
    (u : unused (used_image a)) :
    unused_image_uniform hr a u =
      1 / ((Fintype.card H - r : Nat) : NNReal) := by
  letI : Nonempty (unused (used_image a)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  change Dist.uniform (unused (used_image a)) u = _
  rw [Dist.uniform_apply, unused_card]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

private theorem extend_one_embedding_injective {r : Nat}
    (a : Fin r ↪ H) :
    Function.Injective (extend_one_embedding a) := by
  intro u v huv
  apply Subtype.ext
  simpa [extend_one_embedding, embedding_extension_snoc] using
    congrArg (fun e : Fin (r + 1) ↪ H => e (Fin.last r)) huv

/-- One honest uniform-extension step sends a uniform `r`-embedding to a
uniform `(r+1)`-embedding. -/
private theorem embedding_extension_uniform {r : Nat}
    (hr : r < Fintype.card H) :
    (finite_kernel_comp
      (prefix_embedding_law (Nat.le_of_lt hr))
      (embedding_extension_kernel hr)).val =
      (prefix_embedding_law (Nat.succ_le_of_lt hr)).val := by
  apply Finsupp.ext
  intro e
  let s := embedding_extension_init e
  let a₀ : Fin r ↪ H := s.1.1
  let u₀ : unused (used_image a₀) := ⟨s.1.2, s.2⟩
  have hext : extend_one_embedding a₀ u₀ = e := by
    simpa [s, a₀, u₀, extend_one_embedding,
      embedding_extension_equiv] using
      (embedding_extension_equiv (H := H) r).apply_symm_apply e
  have hkernel_at :
      embedding_extension_kernel hr a₀ e =
        unused_image_uniform hr a₀ u₀ := by
    change
      Dist.fTransform (extend_one_embedding a₀)
          (unused_image_uniform hr a₀).val e =
        unused_image_uniform hr a₀ u₀
    rw [← hext]
    exact
      Dist.fTransform_injective_apply
        (unused_image_uniform hr a₀).val
        (extend_one_embedding a₀)
        (extend_one_embedding_injective a₀) u₀
  have hkernel_off :
      ∀ a : Fin r ↪ H, a ≠ a₀ →
        embedding_extension_kernel hr a e = 0 := by
    intro a ha
    change
      Dist.fTransform (extend_one_embedding a)
          (unused_image_uniform hr a).val e = 0
    apply Dist.fTransform_apply_of_forall_ne
    intro u hue
    apply ha
    have hinit :=
      congrArg
        (fun e' : Fin (r + 1) ↪ H =>
          (embedding_extension_init e').1.1)
        hue
    have hleft :
        (embedding_extension_init
          (extend_one_embedding a u)).1.1 = a := by
      simpa [extend_one_embedding, embedding_extension_equiv] using
        congrArg
          (fun t : embedding_extension_sample (H := H) r => t.1.1)
          ((embedding_extension_equiv (H := H) r).left_inv
            ⟨(a, u.1), u.2⟩)
    exact hleft.symm.trans (by
      simpa [a₀, s] using hinit)
  rw [finite_kernel_comp_apply]
  rw [Finset.sum_eq_single a₀]
  · rw [hkernel_at, prefix_embedding_law_apply,
      unused_image_uniform_apply, prefix_embedding_law_apply,
      Nat.descFactorial_succ]
    have hdf :
        (((Fintype.card H).descFactorial r : Nat) : NNReal) ≠ 0 := by
      exact_mod_cast
        (Nat.descFactorial_pos.mpr (Nat.le_of_lt hr)).ne'
    have hnr :
        ((Fintype.card H - r : Nat) : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hr).ne'
    push_cast
    field_simp [hdf, hnr]
  · intro a _ ha
    rw [hkernel_off a ha]
    simp
  · simp

private abbrev online_state (r : Nat) :=
  hidden_prefix (H := H) r × (Fin r → H)

private def online_agrees {r : Nat} (s : online_state (H := H) r) : Prop :=
  ∀ i, s.1.1 i + s.1.2 i = s.2 i

private def extend_hidden_prefix {r : Nat}
    (p : hidden_prefix (H := H) r) (u : available_pair p.1 p.2) :
    hidden_prefix (H := H) (r + 1) :=
  (embedding_extension_snoc
      ⟨(p.1, u.1.1), u.1.2⟩,
    embedding_extension_snoc
      ⟨(p.2, u.2.1), u.2.2⟩)

private def extend_online_state {r : Nat}
    (s : online_state (H := H) r)
    (w : available_pair s.1.1 s.1.2 × H) :
    online_state (H := H) (r + 1) :=
  (extend_hidden_prefix s.1 w.1, Fin.snoc s.2 w.2)

/-- Agreement after extension is exactly old agreement plus agreement of the
newly coupled outputs. -/
private theorem online_agrees_extend_iff {r : Nat}
    (s : online_state (H := H) r)
    (w : available_pair s.1.1 s.1.2 × H) :
    online_agrees (extend_online_state s w) ↔
      online_agrees s ∧ available_pair_sum w.1 = w.2 := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [online_agrees, extend_online_state,
        extend_hidden_prefix, embedding_extension_snoc] using
        h i.castSucc
    · simpa [online_agrees, extend_online_state,
        extend_hidden_prefix, embedding_extension_snoc,
        available_pair_sum] using h (Fin.last r)
  · rintro ⟨hold, hlast⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [online_agrees, extend_online_state,
        extend_hidden_prefix, embedding_extension_snoc,
        available_pair_sum] using hlast
    · simpa [online_agrees, extend_online_state,
        extend_hidden_prefix, embedding_extension_snoc] using hold j

private theorem prod_prob_fst
    {A B : Type*} [Fintype A] [Fintype B]
    (X : Dist.ProbDist A) (Y : Dist.ProbDist B) :
    Dist.fTransform Prod.fst (Dist.prodProbDist X Y).val = X.val := by
  apply Finsupp.ext
  intro a
  rw [ftransform_fst_pair_apply]
  simp_rw [Dist.prodProbDist_val, Dist.prod_apply]
  rw [← Finset.mul_sum, ← Dist.weight_eq_sum,
    Y.property.weight_eq, mul_one]

private theorem prod_prob_snd
    {A B : Type*} [Fintype A] [Fintype B]
    (X : Dist.ProbDist A) (Y : Dist.ProbDist B) :
    Dist.fTransform Prod.snd (Dist.prodProbDist X Y).val = Y.val := by
  apply Finsupp.ext
  intro b
  rw [ftransform_snd_pair_apply]
  simp_rw [Dist.prodProbDist_val, Dist.prod_apply]
  rw [← Finset.sum_mul, ← Dist.weight_eq_sum,
    X.property.weight_eq, one_mul]

private theorem ftransform_prod_map_both
    {A B C D : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D]
    (X : Dist A) (Y : Dist B) (f : A → C) (g : B → D) :
    Dist.fTransform (fun p : A × B => (f p.1, g p.2))
        (Dist.prod X Y) =
      Dist.prod (Dist.fTransform f X) (Dist.fTransform g Y) := by
  apply Finsupp.ext
  rintro ⟨c, d⟩
  rw [Dist.fTransform_apply_eq_sum, Dist.prod_apply,
    Dist.fTransform_apply_eq_sum, Dist.fTransform_apply_eq_sum]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Dist.prod_apply]
  by_cases hf : f a = c <;> by_cases hg : g b = d <;>
    simp [hf, hg, Prod.ext_iff]

/-- Independent product laws with independent component kernels compose
componentwise. -/
private theorem finite_kernel_comp_prod
    {A₁ A₂ B₁ B₂ : Type*}
    [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
    (X₁ : Dist.ProbDist A₁) (X₂ : Dist.ProbDist A₂)
    (K₁ : A₁ → Dist.ProbDist B₁) (K₂ : A₂ → Dist.ProbDist B₂) :
    (finite_kernel_comp (Dist.prodProbDist X₁ X₂)
      (fun p => Dist.prodProbDist (K₁ p.1) (K₂ p.2))).val =
      Dist.prod (finite_kernel_comp X₁ K₁).val
        (finite_kernel_comp X₂ K₂).val := by
  apply Finsupp.ext
  rintro ⟨b₁, b₂⟩
  rw [finite_kernel_comp_apply, Dist.prod_apply,
    finite_kernel_comp_apply, finite_kernel_comp_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a₂ _
  simp only [Dist.prodProbDist_val, Dist.prod_apply]
  ring

/-- The uniform available pair is the independent product of the two uniform
unused-image laws. -/
private theorem available_pair_uniform_eq_prod {r : Nat}
    (hr : r < Fintype.card H) (a b : Fin r ↪ H) :
    available_pair_uniform hr a b =
      Dist.prodProbDist
        (unused_image_uniform hr a)
        (unused_image_uniform hr b) := by
  letI : Nonempty (unused (used_image a)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  letI : Nonempty (unused (used_image b)) :=
    unused_nonempty _ (by rw [used_image_card]; exact hr)
  apply Subtype.ext
  change
    Dist.uniform
        (unused (used_image a) × unused (used_image b)) =
      Dist.prod
        (Dist.uniform (unused (used_image a)))
        (Dist.uniform (unused (used_image b)))
  exact Dist.prod_uniform.symm

/-- Honest transition kernel for the pair of hidden injection prefixes. -/
private noncomputable def hidden_extension_kernel {r : Nat}
    (hr : r < Fintype.card H) (p : hidden_prefix (H := H) r) :
    Dist.ProbDist (hidden_prefix (H := H) (r + 1)) :=
  ⟨Dist.fTransform (extend_hidden_prefix p)
      (available_pair_uniform hr p.1 p.2).val,
    Dist.fTransform_isProbDist _
      (available_pair_uniform hr p.1 p.2).property⟩

private theorem hidden_extension_kernel_eq_prod {r : Nat}
    (hr : r < Fintype.card H) (p : hidden_prefix (H := H) r) :
    hidden_extension_kernel hr p =
      Dist.prodProbDist
        (embedding_extension_kernel hr p.1)
        (embedding_extension_kernel hr p.2) := by
  apply Subtype.ext
  change
    Dist.fTransform (extend_hidden_prefix p)
        (available_pair_uniform hr p.1 p.2).val =
      Dist.prod
        (Dist.fTransform (extend_one_embedding p.1)
          (unused_image_uniform hr p.1).val)
        (Dist.fTransform (extend_one_embedding p.2)
          (unused_image_uniform hr p.2).val)
  rw [show (available_pair_uniform hr p.1 p.2).val =
      (Dist.prodProbDist
        (unused_image_uniform hr p.1)
        (unused_image_uniform hr p.2)).val by
      exact congrArg Subtype.val
        (available_pair_uniform_eq_prod hr p.1 p.2)]
  simpa [extend_hidden_prefix, extend_one_embedding] using
    ftransform_prod_map_both
      (unused_image_uniform hr p.1).val
      (unused_image_uniform hr p.2).val
      (extend_one_embedding p.1)
      (extend_one_embedding p.2)

private theorem prefix_embedding_pair_law_eq_prod {r : Nat}
    (hr : r ≤ Fintype.card H) :
    prefix_embedding_pair_law hr =
      Dist.prodProbDist
        (prefix_embedding_law hr)
        (prefix_embedding_law hr) := by
  letI : Nonempty (Fin r ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  apply Subtype.ext
  change
    Dist.uniform ((Fin r ↪ H) × (Fin r ↪ H)) =
      Dist.prod
        (Dist.uniform (Fin r ↪ H))
        (Dist.uniform (Fin r ↪ H))
  exact Dist.prod_uniform.symm

/-- The pair-valued honest hidden transition preserves the uniform pair of
injection prefixes. -/
private theorem hidden_extension_uniform {r : Nat}
    (hr : r < Fintype.card H) :
    (finite_kernel_comp
      (prefix_embedding_pair_law (Nat.le_of_lt hr))
      (hidden_extension_kernel hr)).val =
      (prefix_embedding_pair_law
        (Nat.succ_le_of_lt hr)).val := by
  let oldSingle := prefix_embedding_law (H := H) (Nat.le_of_lt hr)
  let newSingle := prefix_embedding_law (H := H) (Nat.succ_le_of_lt hr)
  calc
    (finite_kernel_comp
        (prefix_embedding_pair_law (Nat.le_of_lt hr))
        (hidden_extension_kernel hr)).val =
      (finite_kernel_comp
        (Dist.prodProbDist oldSingle oldSingle)
        (fun p =>
          Dist.prodProbDist
            (embedding_extension_kernel hr p.1)
            (embedding_extension_kernel hr p.2))).val := by
          apply Finsupp.ext
          intro t
          rw [finite_kernel_comp_apply, finite_kernel_comp_apply]
          have hbase :=
            prefix_embedding_pair_law_eq_prod
              (H := H) (Nat.le_of_lt hr)
          apply Finset.sum_congr rfl
          intro p _
          rw [show prefix_embedding_pair_law
              (H := H) (Nat.le_of_lt hr) p =
              Dist.prodProbDist oldSingle oldSingle p by
                exact congrArg (fun D : Dist.ProbDist _ => D p) hbase]
          rw [show hidden_extension_kernel hr p t =
              Dist.prodProbDist
                (embedding_extension_kernel hr p.1)
                (embedding_extension_kernel hr p.2) t by
                exact congrArg (fun D : Dist.ProbDist _ => D t)
                  (hidden_extension_kernel_eq_prod hr p)]
    _ = Dist.prod
          (finite_kernel_comp oldSingle
            (embedding_extension_kernel hr)).val
          (finite_kernel_comp oldSingle
            (embedding_extension_kernel hr)).val :=
      finite_kernel_comp_prod oldSingle oldSingle
        (embedding_extension_kernel hr)
        (embedding_extension_kernel hr)
    _ = Dist.prod newSingle.val newSingle.val := by
          rw [show
            (finite_kernel_comp oldSingle
              (embedding_extension_kernel hr)).val =
                newSingle.val by
              exact embedding_extension_uniform hr]
    _ = (prefix_embedding_pair_law
          (Nat.succ_le_of_lt hr)).val := by
          exact
            (congrArg Subtype.val
              (prefix_embedding_pair_law_eq_prod
                (H := H) (Nat.succ_le_of_lt hr))).symm

/-- One honest step.  The good branch uses the maximal output coupling; the
bad branch continues the two marginals independently. -/
private noncomputable def state_step_joint {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    Dist.ProbDist (available_pair s.1.1 s.1.2 × H) :=
  if online_agrees s then
    coupled_fresh_step hr s.1.1 s.1.2
  else
    Dist.prodProbDist
      (available_pair_uniform hr s.1.1 s.1.2)
      ⟨Dist.uniform H, Dist.uniform_isProbDist⟩

private theorem state_step_joint_fst {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    Dist.fTransform Prod.fst (state_step_joint hr s).val =
      (available_pair_uniform hr s.1.1 s.1.2).val := by
  by_cases h : online_agrees s
  · simp only [state_step_joint, h, if_pos]
    exact coupled_fresh_step_fst hr s.1.1 s.1.2
  · simp only [state_step_joint, h, if_neg]
    exact
      prod_prob_fst
        (available_pair_uniform hr s.1.1 s.1.2)
        ⟨Dist.uniform H, Dist.uniform_isProbDist⟩

private theorem state_step_joint_snd {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    Dist.fTransform Prod.snd (state_step_joint hr s).val =
      Dist.uniform H := by
  by_cases h : online_agrees s
  · simp only [state_step_joint, h, if_pos]
    exact coupled_fresh_step_snd hr s.1.1 s.1.2
  · simp only [state_step_joint, h, if_neg]
    exact
      prod_prob_snd
        (available_pair_uniform hr s.1.1 s.1.2)
        ⟨Dist.uniform H, Dist.uniform_isProbDist⟩

private noncomputable def online_kernel {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    Dist.ProbDist (online_state (H := H) (r + 1)) :=
  ⟨Dist.fTransform (extend_online_state s) (state_step_joint hr s).val,
    Dist.fTransform_isProbDist _ (state_step_joint hr s).property⟩

/-- The real hidden-coordinate transition is uniform over the two unused
images, independently of the ideal tape and of whether failure occurred. -/
private theorem online_kernel_real {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    Dist.fTransform (fun t : online_state (H := H) (r + 1) => t.1)
        (online_kernel hr s).val =
      Dist.fTransform (extend_hidden_prefix s.1)
        (available_pair_uniform hr s.1.1 s.1.2).val := by
  change
    Dist.fTransform (fun t : online_state (H := H) (r + 1) => t.1)
        (Dist.fTransform (extend_online_state s)
          (state_step_joint hr s).val) = _
  rw [Dist.fTransform_comp]
  change
    Dist.fTransform (extend_hidden_prefix s.1 ∘ Prod.fst)
        (state_step_joint hr s).val = _
  rw [← Dist.fTransform_comp, state_step_joint_fst]

/-- The ideal transition appends a fresh uniform coordinate, independently of
the entire current state. -/
private theorem online_kernel_ideal {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    Dist.fTransform (fun t : online_state (H := H) (r + 1) => t.2)
        (online_kernel hr s).val =
      Dist.fTransform (fun z : H => Fin.snoc s.2 z) (Dist.uniform H) := by
  change
    Dist.fTransform (fun t : online_state (H := H) (r + 1) => t.2)
        (Dist.fTransform (extend_online_state s)
          (state_step_joint hr s).val) = _
  rw [Dist.fTransform_comp]
  change
    Dist.fTransform
        (fun w : available_pair s.1.1 s.1.2 × H =>
          @Fin.snoc r (fun _ => H) s.2 w.2)
        (state_step_joint hr s).val = _
  calc
    Dist.fTransform
        (fun w : available_pair s.1.1 s.1.2 × H =>
          @Fin.snoc r (fun _ => H) s.2 w.2)
        (state_step_joint hr s).val =
      Dist.fTransform
          (fun z : H => @Fin.snoc r (fun _ => H) s.2 z)
          (Dist.fTransform Prod.snd (state_step_joint hr s).val) := by
            rw [Dist.fTransform_comp]
            rfl
    _ = _ := by rw [state_step_joint_snd]

/-- The recursively composed honest joint state. -/
private noncomputable def online_state_law :
    (r : Nat) → (r ≤ Fintype.card H) →
      Dist.ProbDist (online_state (H := H) r)
  | 0, _ => ⟨Dist.uniform (online_state (H := H) 0),
      Dist.uniform_isProbDist⟩
  | r + 1, hr =>
      finite_kernel_comp
        (online_state_law r (Nat.le_trans (Nat.le_succ r) hr))
        (online_kernel (Nat.lt_of_succ_le hr))

/-- First marginal of the complete recursive state: two independent uniform
injective image prefixes. -/
private theorem online_state_law_real_marginal
    (r : Nat) (hr : r ≤ Fintype.card H) :
    Dist.fTransform (fun s : online_state (H := H) r => s.1)
        (online_state_law r hr).val =
      (prefix_embedding_pair_law hr).val := by
  induction r with
  | zero =>
      change
        Dist.fTransform Prod.fst
            (Dist.uniform
              (hidden_prefix (H := H) 0 × (Fin 0 → H))) =
          Dist.uniform (hidden_prefix (H := H) 0)
      exact
        Dist.fTransform_fst_uniform
          (hidden_prefix (H := H) 0) (Fin 0 → H)
  | succ r ih =>
      have hr' : r ≤ Fintype.card H :=
        Nat.le_trans (Nat.le_succ r) hr
      have hstep : r < Fintype.card H :=
        Nat.lt_of_succ_le hr
      letI : Nonempty (Fin r ↪ H) :=
        Function.Embedding.nonempty_of_card_le
          (by simpa using hr')
      let oldLaw := online_state_law r hr'
      let realPrefixLaw : Dist.ProbDist (hidden_prefix (H := H) r) :=
        ⟨Dist.fTransform
            (fun s : online_state (H := H) r => s.1)
            oldLaw.val,
          Dist.fTransform_isProbDist _ oldLaw.property⟩
      have hprefixLaw :
          realPrefixLaw = prefix_embedding_pair_law hr' := by
        apply Subtype.ext
        simpa [realPrefixLaw, oldLaw] using ih hr'
      calc
        Dist.fTransform
            (fun s : online_state (H := H) (r + 1) => s.1)
            (online_state_law (r + 1) hr).val =
          (finite_kernel_comp oldLaw
            (fun s =>
              ⟨Dist.fTransform
                  (fun t : online_state (H := H) (r + 1) => t.1)
                  (online_kernel hstep s).val,
                Dist.fTransform_isProbDist _
                  (online_kernel hstep s).property⟩)).val := by
            change
              Dist.fTransform
                  (fun s : online_state (H := H) (r + 1) => s.1)
                  (finite_kernel_comp oldLaw
                    (online_kernel hstep)).val = _
            exact
              ftransform_finite_kernel_comp oldLaw
                (online_kernel hstep)
                (fun s : online_state (H := H) (r + 1) => s.1)
        _ = (finite_kernel_comp oldLaw
              (fun s => hidden_extension_kernel hstep s.1)).val := by
            apply Finsupp.ext
            intro p
            rw [finite_kernel_comp_apply, finite_kernel_comp_apply]
            apply Finset.sum_congr rfl
            intro s _
            exact congrArg (fun x : Real => oldLaw s * x)
              (by
                simpa [hidden_extension_kernel] using
                  congrArg
                    (fun D : Dist (hidden_prefix (H := H) (r + 1)) =>
                      D p)
                    (online_kernel_real hstep s))
        _ =
          (finite_kernel_comp realPrefixLaw
            (hidden_extension_kernel hstep)).val := by
              exact
                finite_kernel_comp_factor oldLaw
                  (fun s : online_state (H := H) r => s.1)
                  (hidden_extension_kernel hstep)
        _ =
          (finite_kernel_comp
            (prefix_embedding_pair_law hr')
            (hidden_extension_kernel hstep)).val := by
              rw [hprefixLaw]
        _ = (prefix_embedding_pair_law hr).val := by
              simpa using hidden_extension_uniform hstep

/-- Append one independent uniform ideal output to a fixed ideal prefix. -/
private noncomputable def ideal_append_kernel {r : Nat}
    (z : Fin r → H) : Dist.ProbDist (Fin (r + 1) → H) :=
  ⟨Dist.fTransform
      (fun x : H => @Fin.snoc r (fun _ => H) z x)
      (Dist.uniform H),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Second marginal of the complete recursive state: an independent uniform
ideal tape. -/
private theorem online_state_law_ideal_marginal
    (r : Nat) (hr : r ≤ Fintype.card H) :
    Dist.fTransform (fun s : online_state (H := H) r => s.2)
        (online_state_law r hr).val =
      Dist.uniform (Fin r → H) := by
  induction r with
  | zero =>
      change
        Dist.fTransform Prod.snd
            (Dist.uniform
              (hidden_prefix (H := H) 0 × (Fin 0 → H))) =
          Dist.uniform (Fin 0 → H)
      exact
        Dist.fTransform_snd_uniform
          (hidden_prefix (H := H) 0) (Fin 0 → H)
  | succ r ih =>
      have hr' : r ≤ Fintype.card H :=
        Nat.le_trans (Nat.le_succ r) hr
      have hstep : r < Fintype.card H :=
        Nat.lt_of_succ_le hr
      letI : Nonempty (Fin r ↪ H) :=
        Function.Embedding.nonempty_of_card_le
          (by simpa using hr')
      let oldLaw := online_state_law r hr'
      let idealPrefixLaw : Dist.ProbDist (Fin r → H) :=
        ⟨Dist.fTransform
            (fun s : online_state (H := H) r => s.2)
            oldLaw.val,
          Dist.fTransform_isProbDist _ oldLaw.property⟩
      let uniformPrefixLaw : Dist.ProbDist (Fin r → H) :=
        ⟨Dist.uniform (Fin r → H), Dist.uniform_isProbDist⟩
      have hprefixLaw : idealPrefixLaw = uniformPrefixLaw := by
        apply Subtype.ext
        simpa [idealPrefixLaw, uniformPrefixLaw, oldLaw] using ih hr'
      calc
        Dist.fTransform
            (fun s : online_state (H := H) (r + 1) => s.2)
            (online_state_law (r + 1) hr).val =
          (finite_kernel_comp oldLaw
            (fun s =>
              ⟨Dist.fTransform
                  (fun t : online_state (H := H) (r + 1) => t.2)
                  (online_kernel hstep s).val,
                Dist.fTransform_isProbDist _
                  (online_kernel hstep s).property⟩)).val := by
            change
              Dist.fTransform
                  (fun s : online_state (H := H) (r + 1) => s.2)
                  (finite_kernel_comp oldLaw
                    (online_kernel hstep)).val = _
            exact
              ftransform_finite_kernel_comp oldLaw
                (online_kernel hstep)
                (fun s : online_state (H := H) (r + 1) => s.2)
        _ = (finite_kernel_comp oldLaw
              (fun s => ideal_append_kernel s.2)).val := by
            apply Finsupp.ext
            intro z
            rw [finite_kernel_comp_apply, finite_kernel_comp_apply]
            apply Finset.sum_congr rfl
            intro s _
            exact congrArg (fun x : Real => oldLaw s * x)
              (by
                simpa [ideal_append_kernel] using
                  congrArg
                    (fun D : Dist (Fin (r + 1) → H) => D z)
                    (online_kernel_ideal hstep s))
        _ =
          (finite_kernel_comp idealPrefixLaw
            ideal_append_kernel).val := by
              exact
                finite_kernel_comp_factor oldLaw
                  (fun s : online_state (H := H) r => s.2)
                  ideal_append_kernel
        _ =
          (finite_kernel_comp uniformPrefixLaw
            ideal_append_kernel).val := by
              rw [hprefixLaw]
        _ =
          Dist.fTransform snoc_tape
            (Dist.prod
              (Dist.uniform (Fin r → H))
              (Dist.uniform H)) := by
              change
                (finite_kernel_comp
                  ⟨Dist.uniform (Fin r → H),
                    Dist.uniform_isProbDist⟩
                  ideal_append_kernel).val = _
              exact
                finite_kernel_comp_map_prod
                  ⟨Dist.uniform (Fin r → H),
                    Dist.uniform_isProbDist⟩
                  ⟨Dist.uniform H, Dist.uniform_isProbDist⟩
                  (fun z x => @Fin.snoc r (fun _ => H) z x)
        _ = Dist.uniform (Fin (r + 1) → H) :=
          snoc_uniform_tape r

/-- State-independent upper bound for the fresh mismatch at rank `r`. -/
private def sequential_step_error (H : Type*) [Fintype H]
    (r : Nat) : NNReal :=
  ((r * r : Nat) : NNReal) /
    (((Fintype.card H) * (Fintype.card H - r) : Nat) : NNReal)

/-- The actual one-step failure parameter.  Capping at one is immaterial in
`1 - d_r`, but makes the product estimate a literal product of probabilities. -/
private def sequential_step_failure (H : Type*) [Fintype H]
    (r : Nat) : NNReal :=
  min 1 (sequential_step_error H r)

/-- Conditional failure bound for one transition of the actual online joint. -/
private theorem online_kernel_failure_le {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    (online_kernel hr s).val.mass
        (fun t => ¬ online_agrees t) ≤
      if online_agrees s then sequential_step_failure H r else 1 := by
  by_cases hs : online_agrees s
  · rw [if_pos hs]
    change
      (Dist.fTransform (extend_online_state s)
        (state_step_joint hr s).val).mass
          (fun t => ¬ online_agrees t) ≤ _
    rw [Dist.mass_fTransform]
    have hevent :
        (fun w : available_pair s.1.1 s.1.2 × H =>
          ¬ online_agrees (extend_online_state s w)) =
        (fun w => available_pair_sum w.1 ≠ w.2) := by
      funext w
      simp [online_agrees_extend_iff, hs]
    rw [hevent]
    change
      (state_step_joint hr s).val.mass
          (fun w => available_pair_sum w.1 ≠ w.2) ≤ _
    rw [show state_step_joint hr s =
        coupled_fresh_step hr s.1.1 s.1.2 by
      simp [state_step_joint, hs]]
    rw [coupled_fresh_step_disagreement]
    exact le_min
      (by
        calc
          RandomSystems.statDist
              (real_next_output hr s.1.1 s.1.2).val
              (Dist.uniform H) ≤
            (real_next_output hr s.1.1 s.1.2).val.weight :=
              RandomSystems.statDist_le_weight
                (real_next_output hr s.1.1 s.1.2).property.nonNeg
                Dist.uniform_nonNeg
          _ = 1 :=
            (real_next_output hr s.1.1 s.1.2).property.weight_eq)
      (real_next_output_distance_le hr s.1.1 s.1.2)
  · rw [if_neg hs]
    exact Dist.mass_le_one (online_kernel hr s).property _

/-- At an agreeing state, one transition preserves agreement with probability
at least `1 - d_r`; after failure the lower bound is zero. -/
private theorem online_kernel_agreement_ge {r : Nat}
    (hr : r < Fintype.card H) (s : online_state (H := H) r) :
    (if online_agrees s then
        (1 : Real) - (sequential_step_failure H r : Real)
      else 0) ≤
      (online_kernel hr s).val.mass online_agrees := by
  by_cases hs : online_agrees s
  · rw [if_pos hs]
    have hfail := online_kernel_failure_le hr s
    rw [if_pos hs] at hfail
    have hpartition :=
      Dist.mass_add_compl (online_kernel hr s).val online_agrees
    rw [(online_kernel hr s).property.weight_eq] at hpartition
    have hagree :
        (online_kernel hr s).val.mass online_agrees =
          1 -
            (online_kernel hr s).val.mass
              (fun t => ¬ online_agrees t) :=
      eq_sub_of_add_eq hpartition
    rw [hagree]
    exact sub_le_sub_left hfail 1
  · rw [if_neg hs]
    exact (online_kernel hr s).property.nonNeg.mass_nonneg _

/-- The surviving agreement mass is multiplicative across one honest
transition. -/
private theorem online_state_law_agreement_succ_ge {r : Nat}
    (hr : r < Fintype.card H) :
    (online_state_law r (Nat.le_of_lt hr)).val.mass online_agrees *
        (1 - sequential_step_failure H r) ≤
      (online_state_law (r + 1) (Nat.succ_le_of_lt hr)).val.mass
        online_agrees := by
  let oldLaw := online_state_law r (Nat.le_of_lt hr)
  change
    oldLaw.val.mass online_agrees *
        (1 - sequential_step_failure H r) ≤
      (finite_kernel_comp oldLaw (online_kernel hr)).val.mass
        online_agrees
  rw [finite_kernel_comp_mass]
  calc
    oldLaw.val.mass online_agrees *
        (1 - sequential_step_failure H r) =
      ∑ s : online_state (H := H) r,
        oldLaw s *
          (if online_agrees s then
            (1 : Real) - (sequential_step_failure H r : Real)
          else 0) := by
        rw [Dist.mass_eq_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : online_agrees s <;> simp [hs]
    _ ≤
      ∑ s : online_state (H := H) r,
        oldLaw s *
          (online_kernel hr s).val.mass online_agrees :=
        Finset.sum_le_sum (fun s _ =>
          mul_le_mul_of_nonneg_left
            (online_kernel_agreement_ge hr s)
            (oldLaw.property.nonNeg s))

/-- Proposition 8, multiplicative clause: the probability that every coupled
answer still agrees is at least the product of the one-step survival
probabilities. -/
private theorem online_state_law_agreement_ge_product
    (q : Nat) (hq : q ≤ Fintype.card H) :
    ∏ r : Fin q,
        ((1 : Real) - (sequential_step_failure H r.1 : Real)) ≤
      (online_state_law q hq).val.mass online_agrees := by
  induction q with
  | zero =>
      have hall :
          ∀ s : online_state (H := H) 0, online_agrees s := by
        intro s i
        exact Fin.elim0 i
      have hmass :
          (online_state_law 0 hq).val.mass online_agrees = 1 := by
        calc
          (online_state_law 0 hq).val.mass online_agrees =
              (online_state_law 0 hq).val.mass (fun _ => True) :=
            Dist.mass_congr _ (fun s => iff_true_intro (hall s))
          _ = (online_state_law 0 hq).val.weight :=
            Dist.mass_true _
          _ = 1 := (online_state_law 0 hq).property.weight_eq
      simpa [hmass]
  | succ q ih =>
      have hstep : q < Fintype.card H := by omega
      have hcap : sequential_step_failure H q ≤ 1 :=
        min_le_left _ _
      have hsurvive_nonneg :
          0 ≤ (1 : Real) - (sequential_step_failure H q : Real) :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr hcap)
      rw [Fin.prod_univ_castSucc]
      calc
        (∏ r : Fin q,
            ((1 : Real) - (sequential_step_failure H r.1 : Real))) *
              ((1 : Real) - (sequential_step_failure H q : Real)) ≤
          (online_state_law q (Nat.le_of_lt hstep)).val.mass
              online_agrees *
            ((1 : Real) - (sequential_step_failure H q : Real)) :=
          mul_le_mul_of_nonneg_right
            (ih (Nat.le_of_lt hstep)) hsurvive_nonneg
        _ ≤
          (online_state_law (q + 1) hq).val.mass
            online_agrees := by
          simpa using online_state_law_agreement_succ_ge hstep

/-- Proposition 8's product failure bound for the recursive joint. -/
private theorem online_state_law_failure_le_product
    (q : Nat) (hq : q ≤ Fintype.card H) :
    (online_state_law q hq).val.mass
        (fun s => ¬ online_agrees s) ≤
      1 - ∏ r : Fin q,
        ((1 : Real) - (sequential_step_failure H r.1 : Real)) := by
  have hpartition :=
    Dist.mass_add_compl (online_state_law q hq).val online_agrees
  rw [(online_state_law q hq).property.weight_eq] at hpartition
  have hfailure :
      (online_state_law q hq).val.mass
          (fun s => ¬ online_agrees s) =
        1 - (online_state_law q hq).val.mass online_agrees :=
    eq_sub_of_add_eq (by simpa [add_comm] using hpartition)
  rw [hfailure]
  exact
    sub_le_sub_left
      (online_state_law_agreement_ge_product q hq) 1

/-- The product failure bound is no larger than the additive one-step bound.
This is the Weierstrass inequality, applied only to the probabilities
`d_r = min 1 e_r`. -/
private theorem sequential_failure_product_le_sum
    (q : Nat) :
    1 - ∏ r : Fin q, (1 - sequential_step_failure H r.1) ≤
      ∑ r : Fin q, sequential_step_error H r.1 := by
  have hcap :
      ∀ r : Fin q, sequential_step_failure H r.1 ≤ 1 :=
    fun r => min_le_left _ _
  have hprod :
      ∏ r : Fin q, (1 - sequential_step_failure H r.1) ≤ 1 :=
    Finset.prod_le_one
      (fun _ _ => zero_le _)
      (fun r _ => tsub_le_self)
  have hweier :=
    CR18.Counting.one_sub_sum_le_prod_one_sub Finset.univ
      (fun r : Fin q => (sequential_step_failure H r.1 : ℝ))
      (fun r _ => NNReal.coe_nonneg (sequential_step_failure H r.1))
      (fun r _ => NNReal.coe_le_coe.mpr (hcap r))
  have hproduct_to_cap :
      1 - ∏ r : Fin q, (1 - sequential_step_failure H r.1) ≤
        ∑ r : Fin q, sequential_step_failure H r.1 := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sub hprod, NNReal.coe_prod, NNReal.coe_sum]
    simp_rw [NNReal.coe_sub (hcap _)]
    simp only [NNReal.coe_one]
    linarith
  exact hproduct_to_cap.trans
    (Finset.sum_le_sum (fun r _ => min_le_right _ _))

/-- Visible real/ideal tapes carried by an online state. -/
private def online_tape_pair {q : Nat}
    (s : online_state (H := H) q) :
    (Fin q → H) × (Fin q → H) :=
  ((fun i => s.1.1 i + s.1.2 i), s.2)

/-- Proposition 8's explicit sequential coupling at fresh-tape level. -/
private noncomputable def sequential_prefix_coupling
    (q : Nat) (hq : q ≤ Fintype.card H) :
    DistCoupling
      (real_prefix_tape hq).val
      (Dist.uniform (Fin q → H)) where
  joint :=
    Dist.fTransform online_tape_pair
      (online_state_law q hq).val
  nonneg := (online_state_law q hq).property.nonNeg.fTransform _
  marginal_fst := by
    rw [Dist.fTransform_comp]
    change
      Dist.fTransform
          ((fun p : hidden_prefix (H := H) q =>
            fun i => p.1 i + p.2 i) ∘
            (fun s : online_state (H := H) q => s.1))
          (online_state_law q hq).val =
        (real_prefix_tape hq).val
    rw [← Dist.fTransform_comp,
      online_state_law_real_marginal]
    exact (real_prefix_tape_eq_pair_pushforward hq).symm
  marginal_snd := by
    rw [Dist.fTransform_comp]
    change
      Dist.fTransform (fun s : online_state (H := H) q => s.2)
          (online_state_law q hq).val =
        Dist.uniform (Fin q → H)
    exact online_state_law_ideal_marginal q hq

/-- The tape disagreement of the explicit sequential coupling is exactly the
absorbing failure event of its recursive state. -/
private theorem sequential_prefix_coupling_disagreement {q : Nat}
    (hq : q ≤ Fintype.card H) :
    (sequential_prefix_coupling q hq).prDisagree =
      (online_state_law q hq).val.mass
        (fun s => ¬ online_agrees s) := by
  have hpr :
      (sequential_prefix_coupling q hq).prDisagree =
        (sequential_prefix_coupling q hq).joint.mass
          (fun p => p.1 ≠ p.2) := by
    rw [Dist.mass_eq_sum, DistCoupling.prDisagree,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.1 ≠ p.2 <;> simp [hp]
  rw [hpr]
  change
    (Dist.fTransform online_tape_pair
      (online_state_law q hq).val).mass
        (fun p => p.1 ≠ p.2) = _
  rw [Dist.mass_fTransform]
  apply Dist.mass_congr
  intro s
  simp only [online_tape_pair, online_agrees]
  constructor
  · intro hneq hagree
    apply hneq
    funext i
    exact hagree i
  · intro hnot heq
    apply hnot
    intro i
    exact congrFun heq i

/-- Proposition 8, product disagreement theorem for the explicit sequential
tape coupling. -/
private theorem sequential_prefix_coupling_disagreement_le_product
    (q : Nat) (hq : q ≤ Fintype.card H) :
    (sequential_prefix_coupling q hq).prDisagree ≤
      1 - ∏ r : Fin q,
        ((1 : Real) - (sequential_step_failure H r.1 : Real)) := by
  rw [sequential_prefix_coupling_disagreement]
  exact online_state_law_failure_le_product q hq

end SequentialOneStep

/-!
### Public numerical security surface

Everything above this point in the numerical argument is proof
infrastructure: hidden image prefixes, available-pair fibers, and the
statewise coupling.  The public endpoint below deliberately forgets those
objects.  It speaks only about the adaptive distinguishing advantage of the
two concrete law-level oracles and an explicit parameter-only bound.
-/

/-- The honest uniform-embedding prefix presentation is the same law as the
literal permutation-sum fresh tape. -/
private theorem real_prefix_tape_eq_real_fresh_tape {q : Nat}
    (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    (real_prefix_tape hq).val =
      (real_fresh_tape G xs).val := by
  apply Finsupp.ext
  intro y
  rw [real_prefix_tape_apply,
    real_fresh_tape_apply G hq xs]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

/-- Proposition 8 transported from the honest hidden-prefix presentation to
the concrete literal-sum fresh tape. -/
noncomputable def sequential_tape_coupling {q : Nat}
    (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    DistCoupling
      (real_fresh_tape G xs).val
      (ideal_fresh_tape G q).val where
  joint := (sequential_prefix_coupling q hq).joint
  nonneg := (sequential_prefix_coupling q hq).nonneg
  marginal_fst := by
    calc
      Dist.fTransform Prod.fst
          (sequential_prefix_coupling q hq).joint =
        (real_prefix_tape hq).val :=
          (sequential_prefix_coupling q hq).marginal_fst
      _ = (real_fresh_tape G xs).val :=
        real_prefix_tape_eq_real_fresh_tape G hq xs
  marginal_snd := by
    change
      Dist.fTransform Prod.snd
          (sequential_prefix_coupling q hq).joint =
        Dist.uniform (Fin q → G)
    exact (sequential_prefix_coupling q hq).marginal_snd

/-- First marginal audit of the concrete sequential tape coupling. -/
theorem sequential_tape_coupling_fst {q : Nat}
    (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    Dist.fTransform Prod.fst
        (sequential_tape_coupling G hq xs).joint =
      (real_fresh_tape G xs).val :=
  (sequential_tape_coupling G hq xs).marginal_fst

/-- Second marginal audit of the concrete sequential tape coupling. -/
theorem sequential_tape_coupling_snd {q : Nat}
    (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    Dist.fTransform Prod.snd
        (sequential_tape_coupling G hq xs).joint =
      (ideal_fresh_tape G q).val :=
  (sequential_tape_coupling G hq xs).marginal_snd

/-- Proposition 8, product disagreement clause for the concrete honest tape
coupling. -/
theorem sequential_tape_coupling_disagreement_le_product {q : Nat}
    (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    (sequential_tape_coupling G hq xs).prDisagree ≤
      1 - ∏ r : Fin q,
        (1 - min 1
          (((r.1 * r.1 : Nat) : NNReal) /
            (((Fintype.card G) *
              (Fintype.card G - r.1) : Nat) : NNReal))) := by
  change
    (sequential_prefix_coupling q hq).prDisagree ≤ _
  simpa [sequential_step_failure, sequential_step_error] using
    sequential_prefix_coupling_disagreement_le_product
      (H := G) q hq

/-- Proposition 8, additive disagreement clause for the concrete honest tape
coupling. -/
theorem sequential_tape_coupling_disagreement_le_sum {q : Nat}
    (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    (sequential_tape_coupling G hq xs).prDisagree ≤
      ∑ r : Fin q,
        ((r.1 * r.1 : Nat) : NNReal) /
          (((Fintype.card G) *
            (Fintype.card G - r.1) : Nat) : NNReal) := by
  apply
    (sequential_tape_coupling_disagreement_le_product
      G hq xs).trans
  have hNN :
      1 - ∏ r : Fin q,
          (1 - min 1
            (((r.1 * r.1 : Nat) : NNReal) /
              (((Fintype.card G) *
                (Fintype.card G - r.1) : Nat) : NNReal))) ≤
        ∑ r : Fin q,
          ((r.1 * r.1 : Nat) : NNReal) /
            (((Fintype.card G) *
              (Fintype.card G - r.1) : Nat) : NNReal) := by
    simpa [sequential_step_failure, sequential_step_error] using
      sequential_failure_product_le_sum (H := G) q
  have hprod :
      ∏ r : Fin q,
          (1 - min 1
            (((r.1 * r.1 : Nat) : NNReal) /
              (((Fintype.card G) *
                (Fintype.card G - r.1) : Nat) : NNReal))) ≤ 1 :=
    Finset.prod_le_one
      (fun _ _ => zero_le _)
      (fun _ _ => tsub_le_self)
  have hR := NNReal.coe_le_coe.mpr hNN
  rw [NNReal.coe_sub hprod, NNReal.coe_one] at hR
  exact hR

/-- Coupling domination for the concrete law-level systems: every adaptive
environment is bounded by the actual disagreement event of the explicit
sequential coupling. -/
theorem sop_advantage_le_sequential_coupling_disagreement
    (q : Nat) (hq : q ≤ Fintype.card G) (xs : Fin q ↪ G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) ≤
      ((sequential_tape_coupling G hq xs).prDisagree : ℝ) := by
  apply
    Common.TapeRepresentative.adaptive_advantage_le_coupling
      (position_tape_representative G q)
      (xop G) (urf G)
      (real_fresh_tape G xs) (ideal_fresh_tape G q)
      (sequential_tape_coupling G hq xs)
  · intro E
    simpa [Common.TapeRepresentative.prob,
      position_tape_representative, position_tape_prob] using
      xop_transcript_eq_position_tape G hq xs E.1
  · intro E
    simpa [Common.TapeRepresentative.prob,
      position_tape_representative, position_tape_prob] using
      urf_transcript_eq_position_tape G E.1

/-- The direct sequential coupling gives the residual-free explicit sum
bound on adaptive distinguishing advantage. -/
theorem sop_advantage_le_sequential_coupling_sum
    (q : Nat) (hq : q ≤ Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) ≤
      ((∑ r : Fin q,
        ((r.1 * r.1 : Nat) : NNReal) /
          (((Fintype.card G) *
            (Fintype.card G - r.1) : Nat) : NNReal) :
        NNReal) : ℝ) := by
  let xs : Fin q ↪ G :=
    Classical.choice
      (Function.Embedding.nonempty_of_card_le
        (by simpa using hq))
  exact
    (sop_advantage_le_sequential_coupling_disagreement
      G q hq xs).trans
      (by
        exact_mod_cast
          sequential_tape_coupling_disagreement_le_sum
            G hq xs)

/-!
The remaining work in the main estimate is elementary but worth keeping
explicit.  The cubic-range hypothesis forces every exposed prefix to leave at
least half of the permutation range unused.  This replaces each varying
denominator by a common one, after which the classical sum-of-squares identity
gives the exact polynomial constant.
-/

/-- The cubic range is strong enough to keep twice the largest exposed prefix
below the group size. -/
private theorem four_sq_pred_le_cube (q : Nat) :
    4 * (q - 1) ^ 2 ≤ q ^ 3 := by
  by_cases hq : q < 4
  · interval_cases q <;> norm_num
  · have h4 : (4 : ℝ) ≤ q := by
      exact_mod_cast (Nat.le_of_not_gt hq)
    have hmain :
        0 ≤ ((q : ℝ) - 4) * (q : ℝ) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr h4) (sq_nonneg _)
    have hpred : ((q - 1 : Nat) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    exact_mod_cast (show
      (4 : ℝ) * ((q - 1 : Nat) : ℝ) ^ 2 ≤
          (q : ℝ) ^ 3 by
        rw [hpred]
        nlinarith)

/-- Paper Corollary 9, denominator side condition: `q³ ≤ N²` implies
`2(q-1) ≤ N`. -/
private theorem two_pred_le_of_cube_le_sq
    (q N : Nat) (hcube : q ^ 3 ≤ N ^ 2) :
    2 * (q - 1) ≤ N := by
  have hpoly := four_sq_pred_le_cube q
  by_contra h
  have hlt : N < 2 * (q - 1) := by omega
  have hsq : N ^ 2 < (2 * (q - 1)) ^ 2 :=
    Nat.pow_lt_pow_left hlt (by omega)
  nlinarith

/-- The sum of the first `q` squares, stated over the real numbers in the
normal form needed by the probability bound. -/
private theorem sum_fin_sq_real (q : Nat) :
    (∑ r : Fin q, ((r : Nat) : ℝ) ^ 2) =
      (q : ℝ) * ((q : ℝ) - 1) *
        (2 * (q : ℝ) - 1) / 6 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last,
        Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring

/-- Coercion bridge for the same sum-of-squares identity over `NNReal`. -/
private theorem coe_sum_fin_sq_nnreal (q : Nat) :
    (((∑ r : Fin q,
        ((r : Nat) : NNReal) * ((r : Nat) : NNReal)) :
        NNReal) : ℝ) =
      (q : ℝ) * ((q : ℝ) - 1) *
        (2 * (q : ℝ) - 1) / 6 := by
  calc
    (((∑ r : Fin q,
        ((r : Nat) : NNReal) * ((r : Nat) : NNReal)) :
        NNReal) : ℝ) =
        ∑ r : Fin q,
          ((((r : Nat) : NNReal) *
            ((r : Nat) : NNReal)) : ℝ) := by
      exact NNReal.coe_sum Finset.univ _
    _ = ∑ r : Fin q, ((r : Nat) : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      norm_num [pow_two]
    _ = _ := sum_fin_sq_real q

/-- Paper Corollary 9, numerical core: the sequential disagreement sum is at
most the displayed closed polynomial whenever `q³ ≤ N²`. -/
private theorem sequential_sum_le_closed
    (q N : Nat) (hN : 0 < N)
    (hcube : q ^ 3 ≤ N ^ 2) :
    (∑ r : Fin q,
        ((r * r : Nat) : NNReal) /
          ((N * (N - r) : Nat) : NNReal)) ≤
      ((q * (q - 1) * (2 * q - 1) : Nat) : NNReal) /
        ((3 * N ^ 2 : Nat) : NNReal) := by
  have hhalf : 2 * (q - 1) ≤ N :=
    two_pred_le_of_cube_le_sq q N hcube
  calc
    (∑ r : Fin q,
        ((r * r : Nat) : NNReal) /
          ((N * (N - r) : Nat) : NNReal)) ≤
        ∑ r : Fin q,
          ((2 * (r * r) : Nat) : NNReal) /
            ((N ^ 2 : Nat) : NNReal) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrq : (r : Nat) ≤ q - 1 := by omega
      have h2r : 2 * (r : Nat) ≤ N :=
        le_trans (Nat.mul_le_mul_left 2 hrq) hhalf
      have hrN : (r : Nat) ≤ N := by omega
      have hrN' : (r : Nat) < N := by omega
      have hd1 :
          (0 : NNReal) <
            ((N * (N - (r : Nat)) : Nat) : NNReal) := by
        exact_mod_cast Nat.mul_pos hN
          (Nat.sub_pos_of_lt hrN')
      have hd2 :
          (0 : NNReal) < ((N ^ 2 : Nat) : NNReal) := by
        exact_mod_cast (pow_pos hN 2)
      apply (div_le_div_iff₀ hd1 hd2).2
      have hden : N ≤ 2 * (N - (r : Nat)) := by omega
      have hcross :
          ((r : Nat) * r) * N ^ 2 ≤
            (2 * ((r : Nat) * r)) *
              (N * (N - r)) := by
        calc
          ((r : Nat) * r) * N ^ 2 =
              ((r : Nat) * r * N) * N := by ring
          _ ≤ ((r : Nat) * r * N) *
              (2 * (N - r)) :=
            Nat.mul_le_mul_left _ hden
          _ = (2 * ((r : Nat) * r)) *
              (N * (N - r)) := by ring
      exact_mod_cast hcross
    _ = ((2 : NNReal) / ((N ^ 2 : Nat) : NNReal)) *
          ∑ r : Fin q, ((r * r : Nat) : NNReal) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [div_eq_mul_inv, div_eq_mul_inv]
      norm_num
      ac_rfl
    _ = ((q * (q - 1) * (2 * q - 1) : Nat) : NNReal) /
          ((3 * N ^ 2 : Nat) : NNReal) := by
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_div,
        NNReal.coe_ofNat, NNReal.coe_natCast, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      by_cases hq0 : q = 0
      · subst q
        norm_num
      · have hq1 : 1 ≤ q :=
          Nat.one_le_iff_ne_zero.mpr hq0
        have h2q1 : 1 ≤ 2 * q := by omega
        rw [coe_sum_fin_sq_nnreal]
        rw [Nat.cast_sub hq1, Nat.cast_sub h2q1]
        field_simp
        norm_num [Nat.cast_mul]
        ring

/-- The exact closed numerator is bounded by `2q³`. -/
private theorem closed_le_two_cube (q N : Nat) :
    ((q * (q - 1) * (2 * q - 1) : Nat) : NNReal) /
        ((3 * N ^ 2 : Nat) : NNReal) ≤
      ((2 * q ^ 3 : Nat) : NNReal) /
        ((3 * N ^ 2 : Nat) : NNReal) := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      (show q * (q - 1) * (2 * q - 1) ≤
          2 * q ^ 3 by
        calc
          q * (q - 1) * (2 * q - 1) ≤
              q * q * (2 * q) :=
            Nat.mul_le_mul
              (Nat.mul_le_mul_left q
                (Nat.sub_le q 1))
              (Nat.sub_le (2 * q) 1)
          _ = 2 * q ^ 3 := by ring)
  · positivity

/-- The new headline bound is never larger than the previous
`q³ / N²` benchmark. -/
theorem two_thirds_cubic_le_cubic_benchmark
    (q N : Nat) :
    ((2 * q ^ 3 : Nat) : NNReal) /
        ((3 * N ^ 2 : Nat) : NNReal) ≤
      ((q ^ 3 : Nat) : NNReal) /
        ((N ^ 2 : Nat) : NNReal) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hd1 :
        (0 : NNReal) <
          ((3 * N ^ 2 : Nat) : NNReal) := by
      exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3)
        (pow_pos hNpos 2)
    have hd2 :
        (0 : NNReal) < ((N ^ 2 : Nat) : NNReal) := by
      exact_mod_cast (pow_pos hNpos 2)
    apply (div_le_div_iff₀ hd1 hd2).2
    exact_mod_cast
      (show (2 * q ^ 3) * N ^ 2 ≤
          q ^ 3 * (3 * N ^ 2) by
        calc
          (2 * q ^ 3) * N ^ 2 =
              2 * (q ^ 3 * N ^ 2) := by ring
          _ ≤ 3 * (q ^ 3 * N ^ 2) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = q ^ 3 * (3 * N ^ 2) := by ring)

/-- For positive parameters the factor-`2/3` comparison is strict. -/
theorem two_thirds_cubic_lt_cubic_benchmark
    (q N : Nat) (hq : 0 < q) (hN : 0 < N) :
    ((2 * q ^ 3 : Nat) : NNReal) /
        ((3 * N ^ 2 : Nat) : NNReal) <
      ((q ^ 3 : Nat) : NNReal) /
        ((N ^ 2 : Nat) : NNReal) := by
  have hd1 :
      (0 : NNReal) <
        ((3 * N ^ 2 : Nat) : NNReal) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3)
      (pow_pos hN 2)
  have hd2 :
      (0 : NNReal) < ((N ^ 2 : Nat) : NNReal) := by
    exact_mod_cast (pow_pos hN 2)
  apply (div_lt_div_iff₀ hd1 hd2).2
  exact_mod_cast
    (show (2 * q ^ 3) * N ^ 2 <
        q ^ 3 * (3 * N ^ 2) by
      have hq3 : 0 < q ^ 3 := pow_pos hq 3
      have hN2 : 0 < N ^ 2 := pow_pos hN 2
      calc
        (2 * q ^ 3) * N ^ 2 =
            2 * (q ^ 3 * N ^ 2) := by ring
        _ < 3 * (q ^ 3 * N ^ 2) :=
          Nat.mul_lt_mul_of_pos_right
            (by norm_num) (Nat.mul_pos hq3 hN2)
        _ = q ^ 3 * (3 * N ^ 2) := by ring)

/-!
## 6. Optimal finite analysis

The maximal coupling already gives an exact finite answer.  These endpoints
collect its saturated overlap, one-sided-distance, and half-`L¹` forms after
the audit and the independent sequential benchmark have been established.
-/

/-- Exact all-budget compatible-overlap characterization. -/
theorem sop_advantage_eq_one_sub_compatible_overlap (q : Nat) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      ((1 - compatible_overlap G (min q (Fintype.card G)) :
        NNReal) : ℝ) := by
  rw [adv_prf_eq_visible_stat_dist_min_card G q]
  rw [← adv_prf_eq_visible_stat_dist_of_le_card
    G (min q (Fintype.card G)) (Nat.min_le_right _ _)]
  exact
    sop_advantage_eq_one_sub_compatible_overlap_of_le_card
      G (min q (Fintype.card G)) (Nat.min_le_right _ _)

/-- Exact all-budget one-sided compatible-count sum. -/
theorem sop_advantage_eq_compatible_count_distance (q : Nat) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      ((∑ y : Fin (min q (Fintype.card G)) → G,
        ((compatible_count G y : NNReal) /
            (((Fintype.card G).descFactorial
                (min q (Fintype.card G)) *
              (Fintype.card G).descFactorial
                (min q (Fintype.card G)) : Nat) : NNReal) -
          1 /
            ((Fintype.card G ^ min q (Fintype.card G) : Nat) :
              NNReal))) : NNReal) := by
  rw [adv_prf_eq_visible_stat_dist_min_card G q]
  rw [← adv_prf_eq_visible_stat_dist_of_le_card
    G (min q (Fintype.card G)) (Nat.min_le_right _ _)]
  exact
    sop_advantage_eq_compatible_count_distance_of_le_card
      G (min q (Fintype.card G)) (Nat.min_le_right _ _)

/-- Exact all-budget half-`L¹` compatible-count formula. -/
theorem sop_advantage_eq_half_l1_compatible_count (q : Nat) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) =
      (1 / 2 : ℝ) *
        ∑ y : Fin (min q (Fintype.card G)) → G,
          |(((compatible_count G y : NNReal) /
              (((Fintype.card G).descFactorial
                  (min q (Fintype.card G)) *
                (Fintype.card G).descFactorial
                  (min q (Fintype.card G)) : Nat) : NNReal) :
              NNReal) : ℝ) -
            ((1 /
              ((Fintype.card G ^ min q (Fintype.card G) : Nat) :
                NNReal) : NNReal) : ℝ)| := by
  rw [adv_prf_eq_visible_stat_dist_min_card G q]
  rw [← adv_prf_eq_visible_stat_dist_of_le_card
    G (min q (Fintype.card G)) (Nat.min_le_right _ _)]
  exact
    sop_advantage_eq_half_l1_compatible_count_of_le_card
      G (min q (Fintype.card G)) (Nat.min_le_right _ _)

/-!
## 7. Final law-level distinguishing bound

This is deliberately the last declaration in the file.  Its statement names
only the concrete real and ideal systems, the adaptive query budget, and the
closed numerical bound.  Couplings, tapes, and compatible fibers occur only
inside the preceding proof graph.

The proof is assembled from the following rooted DAG.  Every name displayed
here is a declaration above; subsequent proof work should proceed downward
from the first incomplete node rather than introducing a parallel route.

```text
sop_advantage_closed_bound
├─ range
│  └─ two_pred_le_of_cube_le_sq
│     └─ four_sq_pred_le_cube
├─ coupling
│  └─ sop_advantage_le_sequential_coupling_sum
│     ├─ sop_advantage_le_sequential_coupling_disagreement
│     │  ├─ Lemma 3 honest position-tape representatives
│     │  └─ sequential_tape_coupling
│     │     ├─ online_state_law_real_marginal
│     │     └─ online_state_law_ideal_marginal
│     └─ sequential_tape_coupling_disagreement_le_sum
│        ├─ sequential_tape_coupling_disagreement_le_product
│        │  └─ sequential_prefix_coupling_disagreement_le_product
│        │     └─ online_state_law_failure_le_product
│        │        └─ online_state_law_agreement_ge_product
│        │           └─ online_state_law_agreement_succ_ge
│        │              └─ online_kernel_agreement_ge
│        │                 └─ online_kernel_failure_le
│        │                    ├─ online_agrees_extend_iff
│        │                    └─ coupled_fresh_step_disagreement
│        │                       ├─ next_output_coupling_disagreement
│        │                       └─ real_next_output_distance_le
│        └─ sequential_failure_product_le_sum
│           └─ CR18.Counting.one_sub_sum_le_prod_one_sub
└─ arithmetic
   ├─ sequential_sum_le_closed
   │  ├─ two_pred_le_of_cube_le_sq
   │  └─ coe_sum_fin_sq_nnreal
   │     └─ sum_fin_sq_real
   ├─ closed_le_two_cube
   ├─ two_thirds_cubic_le_cubic_benchmark
   └─ two_thirds_cubic_lt_cubic_benchmark
```
-/

/-- Paper Corollary 9, final law-level security theorem.

The hypothesis `q³ ≤ N²` is precisely the range in which the direct online
coupling leaves at least half of the permutation range unused at every fresh
query.  The conclusion is the complete comparison chain from the exact closed
sum-of-squares bound through the factor-`2/3` cubic estimate to the previous
`q³/N²` benchmark; the final comparison is strict when `q > 0`.  No coupling
state, tape, or compatible fiber occurs in the public statement. -/
theorem sop_advantage_closed_bound
    (q : Nat)
    (hcube : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (xop G) (urf G) ≤
      (((q * (q - 1) * (2 * q - 1) : Nat) : NNReal) /
        ((3 * (Fintype.card G) ^ 2 : Nat) : NNReal) :
        NNReal) ∧
    ((q * (q - 1) * (2 * q - 1) : Nat) : NNReal) /
        ((3 * (Fintype.card G) ^ 2 : Nat) : NNReal) ≤
      ((2 * q ^ 3 : Nat) : NNReal) /
        ((3 * (Fintype.card G) ^ 2 : Nat) : NNReal) ∧
    ((2 * q ^ 3 : Nat) : NNReal) /
        ((3 * (Fintype.card G) ^ 2 : Nat) : NNReal) ≤
      ((q ^ 3 : Nat) : NNReal) /
        (((Fintype.card G) ^ 2 : Nat) : NNReal) ∧
    (0 < q →
      ((2 * q ^ 3 : Nat) : NNReal) /
          ((3 * (Fintype.card G) ^ 2 : Nat) : NNReal) <
        ((q ^ 3 : Nat) : NNReal) /
          (((Fintype.card G) ^ 2 : Nat) : NNReal)) := by
  -- Part I: the direct honest coupling bounds adaptive distinguishing
  -- advantage by the sum of its statewise fresh-query disagreement risks.
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hq : q ≤ Fintype.card G := by
    have :=
      two_pred_le_of_cube_le_sq
        q (Fintype.card G) hcube
    omega
  constructor
  · exact
      (sop_advantage_le_sequential_coupling_sum G q hq).trans
        (NNReal.coe_le_coe.mpr
          (sequential_sum_le_closed
            q (Fintype.card G) hN hcube))
  constructor
  · exact closed_le_two_cube q (Fintype.card G)
  constructor
  · exact two_thirds_cubic_le_cubic_benchmark
      q (Fintype.card G)
  · intro hqpos
    exact two_thirds_cubic_lt_cubic_benchmark
      q (Fintype.card G) hqpos hN


end TwoPermutationSum

end RandomSystems.SoP
