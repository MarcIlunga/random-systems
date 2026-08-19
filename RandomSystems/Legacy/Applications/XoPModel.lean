/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.XoPCombinatorics
import RandomSystems.Legacy.Equiv
import RandomSystems.Legacy.Applications.SoP.Partition
import RandomSystems.Legacy.Applications.SoP.TV
import RandomSystems.Counting
import RandomSystems.Legacy.Instances.URF
import RandomSystems.Instances.URFfunEval
import Mathlib.Data.Fintype.Perm

/-!
# Concrete XoP Systems

This file starts the concrete model layer for XoP.  It defines the real system
from two independent permutations and the ideal system as the repository's
stateless uniform random function `URFfun`.
-/

noncomputable section

open scoped NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Model

open Combinatorics

variable {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Deterministic XoP system induced by a pair of permutations. -/
def xopDDS (π₁ π₂ : Equiv.Perm G) : DDS G G q :=
  DDS.ofFunq (q := q) (fun x => -π₁ x + π₂ x)

/-- The real XoP PDS: sample two independent permutations and answer `-π₁(x)+π₂(x)`. -/
def xopRealPDS : PDS G G q where
  dist :=
    Dist.fTransform
      (fun p : Equiv.Perm G × Equiv.Perm G => xopDDS (q := q) p.1 p.2)
      (Dist.uniform (Equiv.Perm G × Equiv.Perm G))

/-- The ideal PDS: a stateless uniform random function. -/
def xopIdealPDS [Nonempty G] : PDS G G q :=
  Instances.URFfun (X := G) (Y := G) (q := q)

/-- Concrete XoP security instance with an externally supplied bound. -/
def xopSecurityInstance [Nonempty G] (bound : NNReal) :
    @SecurityInstance G G q DDS.instFintype where
  real := xopRealPDS (G := G) (q := q)
  ideal := xopIdealPDS (G := G) (q := q)
  bound := bound

/-- The real XoP PDS is a probability system. -/
theorem xopReal_isProbPDS : (xopRealPDS (G := G) (q := q)).isProbPDS := by
  unfold PDS.isProbPDS xopRealPDS
  exact Dist.fTransform_isProbDist _ Dist.uniform_isProbDist

omit [AddGroup G] in
/-- The ideal XoP PDS is a probability system. -/
theorem xopIdeal_isProbPDS [Nonempty G] : (xopIdealPDS (G := G) (q := q)).isProbPDS := by
  unfold xopIdealPDS Instances.URFfun Instances.URFfunOf PDS.isProbPDS
  exact Dist.fTransform_isProbDist _ Dist.uniform_isProbDist

/-- Hidden tuple induced by a permutation and fixed input sequence. -/
def hiddenTuple (π : Equiv.Perm G) (inputs : Fin q → G) : Fin q → G :=
  fun i => π (inputs i)

omit [AddGroup G] in
/-- Extract the output vector produced by a DDS on fixed inputs. -/
def outputMap (inputs : Fin q → G) (s : DDS G G q) : Fin q → G :=
  fun i => s.respond i (fun j => inputs ⟨j.val,
    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)

omit [AddGroup G] in
/-- Embed an output vector into the transcript with fixed input components. -/
def transcriptEmbed (inputs : Fin q → G) (ys : Fin q → G) : Transcript G G q :=
  fun i => (inputs i, ys i)

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Fixed-input transcripts factor through output-vector extraction. -/
theorem transcript_factors (inputs : Fin q → G) :
    (fun s : DDS G G q => DDS.transcript s inputs) =
      transcriptEmbed inputs ∘ outputMap inputs := by
  funext s i
  simp [DDS.transcript, outputMap, transcriptEmbed]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Fixed-input transcript embedding is injective in the output vector. -/
theorem transcriptEmbed_injective (inputs : Fin q → G) :
    Function.Injective (transcriptEmbed (G := G) (q := q) inputs) := by
  intro ys₁ ys₂ h
  funext i
  exact (Prod.mk.inj (congr_fun h i)).2

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Extracting outputs after fixed-input transcript embedding recovers the output vector. -/
theorem transcriptOutputs_transcriptEmbed (inputs ys : Fin q → G) :
    Combinatorics.transcriptOutputs (transcriptEmbed (G := G) (q := q) inputs ys) = ys := by
  rfl

omit [DecidableEq G] in
/-- The compatible transcript count on an embedded transcript is the visible-output count. -/
theorem compatibleTranscriptCountNNReal_transcriptEmbed
    (inputs ys : Fin q → G) :
    compatibleTranscriptCountNNReal (transcriptEmbed (G := G) (q := q) inputs ys) =
      compatibleCountNNReal ys := by
  rfl

omit [AddGroup G] in
/-- Any fixed-input transcript law is a pushforward of its output-vector law. -/
theorem transcriptDist_eq_output_pushforward (S : PDS G G q) (inputs : Fin q → G) :
    S.transcriptDist inputs =
      Dist.fTransform (transcriptEmbed inputs) (Dist.fTransform (outputMap inputs) S.dist) := by
  simp [PDS.transcriptDist, transcript_factors]
  rw [Dist.fTransform_comp]

omit [AddGroup G] in
/-- A transcript outside the image of `transcriptEmbed inputs` receives zero
mass under any pushforward through that embedding. -/
theorem fTransform_transcriptEmbed_eq_zero_of_not_image
    (D : Dist (Fin q → G)) (inputs : Fin q → G) (t : Transcript G G q)
    (hnot : t ≠ transcriptEmbed inputs (Combinatorics.transcriptOutputs t)) :
    (Dist.fTransform (transcriptEmbed inputs) D) t = 0 := by
  rw [Dist.fTransform_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro ys hys
  have hmem := Finset.mem_filter.mp hys
  have heq : transcriptEmbed inputs ys = t := hmem.2
  exact False.elim (hnot (by rw [← heq]; rfl))

omit [AddGroup G] in
/-- Positive-error sums over transcripts pushed through `transcriptEmbed` reduce
to the corresponding visible-output sum. -/
theorem positiveError_transcriptEmbed_pushforward_eq_visible [Nonempty G]
    (inputs : Fin q → G) (density : Transcript G G q → NNReal) :
    (∑ t : Transcript G G q,
      max
        (density t * (Dist.fTransform (transcriptEmbed inputs) (Dist.uniform (Fin q → G))) t -
          (Dist.fTransform (transcriptEmbed inputs) (Dist.uniform (Fin q → G))) t) 0) =
      ∑ y : Fin q → G,
        max
          (density (transcriptEmbed inputs y) * (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0 := by
  let embed := transcriptEmbed (G := G) (q := q) inputs
  let D := Dist.uniform (Fin q → G)
  let imageSet : Finset (Transcript G G q) := (Finset.univ : Finset (Fin q → G)).image embed
  have hinj : Function.Injective embed := transcriptEmbed_injective inputs
  have hsum_univ :
      (∑ t : Transcript G G q, max (density t * (Dist.fTransform embed D) t -
          (Dist.fTransform embed D) t) 0) =
        ∑ t ∈ imageSet, max (density t * (Dist.fTransform embed D) t -
          (Dist.fTransform embed D) t) 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ imageSet)]
    intro t _ ht_not_image
    have hnot : t ≠ embed (Combinatorics.transcriptOutputs t) := by
      intro ht
      apply ht_not_image
      rw [Finset.mem_image]
      exact ⟨Combinatorics.transcriptOutputs t, Finset.mem_univ _, ht.symm⟩
    have hz : (Dist.fTransform embed D) t = 0 :=
      fTransform_transcriptEmbed_eq_zero_of_not_image (G := G) (q := q) D inputs t hnot
    simp [hz]
  rw [show transcriptEmbed (G := G) (q := q) inputs = embed from rfl]
  rw [show Dist.uniform (Fin q → G) = D from rfl]
  rw [hsum_univ]
  rw [show imageSet = (Finset.univ : Finset (Fin q → G)).image embed from rfl]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro y _
    rw [fTransform_injective_apply (X := D) (f := embed) hinj]
  · intro a _ b _ h
    exact hinj h

/-- The real output-vector law is the pushforward of the uniform permutation-pair law. -/
theorem xopReal_outputDist_eq_pair_pushforward (inputs : Fin q → G) :
    Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist =
      Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G => outputMap inputs (xopDDS (q := q) p.1 p.2))
        (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) := by
  simp [xopRealPDS]
  rw [Dist.fTransform_comp]
  rfl

omit [Fintype G] [DecidableEq G] in
/-- Output-vector extraction from `xopDDS`. -/
theorem outputMap_xopDDS (π₁ π₂ : Equiv.Perm G) (inputs : Fin q → G) :
    outputMap inputs (xopDDS (q := q) π₁ π₂) = fun i => -π₁ (inputs i) + π₂ (inputs i) := by
  funext i
  simp [outputMap, xopDDS, DDS.ofFunq]

omit [Fintype G] [DecidableEq G] in
/-- XoP output equality is equivalent to a shifted hidden-tuple equality. -/
theorem output_eq_iff_hiddenTuple (π₁ π₂ : Equiv.Perm G) (inputs ys : Fin q → G) :
    outputMap inputs (xopDDS (q := q) π₁ π₂) = ys ↔
      hiddenTuple (q := q) π₂ inputs = shifted ys (hiddenTuple (q := q) π₁ inputs) := by
  constructor
  · intro h
    funext i
    have hi := congr_fun h i
    simp [outputMap_xopDDS, hiddenTuple, shifted] at hi ⊢
    rw [← hi]
    simp
  · intro h
    funext i
    have hi := congr_fun h i
    simp [outputMap_xopDDS, hiddenTuple, shifted] at hi ⊢
    rw [hi]
    simp

omit [AddGroup G] in
/-- Reusable permutation fiber count specialized to subtype cardinality. -/
theorem permFiber_card
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (a : Fin q → G) (ha : Function.Injective a) :
    Fintype.card {π : Equiv.Perm G // ∀ i, π (inputs i) = a i} =
      (Fintype.card G - q).factorial := by
  letI : Fintype {π : Equiv.Perm G // ∀ i, π (inputs i) = a i} :=
    Fintype.subtype
      ((Finset.univ : Finset (Equiv.Perm G)).filter (fun π => ∀ i, π (inputs i) = a i))
      (by intro π; simp)
  have hqle : q ≤ Fintype.card G := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective inputs hinputs
  have hcard :
      ((Finset.univ : Finset (Equiv.Perm G)).filter (fun π => ∀ i, π (inputs i) = a i)).card =
        (Fintype.card G - q).factorial :=
      RandomSystems.CR18.Counting.card_perm_fiber inputs hinputs a ha hqle
  rw [← hcard]
  rw [← Fintype.card_subtype (p := fun π : Equiv.Perm G => ∀ i, π (inputs i) = a i)]

/-- Permutation-pair output fiber for a fixed output vector. -/
def outputFiber (inputs ys : Fin q → G) : Type _ :=
  {p : Equiv.Perm G × Equiv.Perm G //
    outputMap inputs (xopDDS (q := q) p.1 p.2) = ys}

/-- Permutations matching a fixed input tuple to a fixed output tuple. -/
def permFiber (inputs a : Fin q → G) : Type _ :=
  {π : Equiv.Perm G // ∀ i, π (inputs i) = a i}

/-- Compatible hidden tuples for a fixed visible output vector. -/
def compatibleFiber (ys : Fin q → G) : Type _ :=
  {a : Fin q → G // CompatibleHiddenState ys a}

local instance compatibleHiddenStateDecidable (ys : Fin q → G) :
    DecidablePred (fun a => CompatibleHiddenState ys a) :=
  fun _ => Classical.propDecidable _

instance outputFiberFintype (inputs ys : Fin q → G) :
    Fintype (outputFiber (G := G) (q := q) inputs ys) :=
  Fintype.subtype
    ((Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
      (fun p => outputMap inputs (xopDDS (q := q) p.1 p.2) = ys))
    (by intro p; simp)

instance permFiberFintype (inputs a : Fin q → G) :
    Fintype (permFiber (G := G) (q := q) inputs a) :=
  Fintype.subtype
    ((Finset.univ : Finset (Equiv.Perm G)).filter (fun π => ∀ i, π (inputs i) = a i))
    (by intro π; simp)

instance compatibleFiberFintype (ys : Fin q → G) :
    Fintype (compatibleFiber (G := G) (q := q) ys) :=
  Fintype.subtype
    ((Finset.univ : Finset (Fin q → G)).filter (fun a => CompatibleHiddenState ys a))
    (by intro a; simp)

omit [AddGroup G] in
/-- `permFiber_card` restated for the named subtype. -/
theorem namedPermFiber_card
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (a : Fin q → G) (ha : Function.Injective a) :
    Fintype.card (permFiber (G := G) (q := q) inputs a) =
      (Fintype.card G - q).factorial := by
  simpa [permFiber] using permFiber_card (G := G) (q := q) inputs hinputs a ha

omit [DecidableEq G] in
/-- The compatible hidden-tuple subtype has cardinality `compatibleCountNat`. -/
theorem compatibleFiber_card_named (ys : Fin q → G) :
    Fintype.card (compatibleFiber (G := G) (q := q) ys) = compatibleCountNat ys := by
  simp [compatibleFiber]

/-- Output fibers decompose by the first hidden tuple. -/
def outputFiberEquivCompatibleSigma
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs) :
    outputFiber (G := G) (q := q) inputs ys ≃
      Sigma (fun a : compatibleFiber (G := G) (q := q) ys =>
        permFiber (G := G) (q := q) inputs a.1 ×
          permFiber (G := G) (q := q) inputs (shifted ys a.1)) where
  toFun p := by
    refine ⟨⟨hiddenTuple (q := q) p.1.1 inputs, ?_⟩, ?_⟩
    · have hshift : hiddenTuple (q := q) p.1.2 inputs =
          shifted ys (hiddenTuple (q := q) p.1.1 inputs) :=
        (output_eq_iff_hiddenTuple (G := G) (q := q) p.1.1 p.1.2 inputs ys).mp p.2
      constructor
      · exact p.1.1.injective.comp hinputs
      · rw [← hshift]
        exact p.1.2.injective.comp hinputs
    · exact
        (⟨p.1.1, by intro i; rfl⟩,
          ⟨p.1.2, by
            intro i
            have hshift : hiddenTuple (q := q) p.1.2 inputs =
                shifted ys (hiddenTuple (q := q) p.1.1 inputs) :=
              (output_eq_iff_hiddenTuple (G := G) (q := q) p.1.1 p.1.2 inputs ys).mp p.2
            exact congr_fun hshift i⟩)
  invFun s := by
    refine ⟨(s.2.1.1, s.2.2.1), ?_⟩
    exact (output_eq_iff_hiddenTuple (G := G) (q := q) s.2.1.1 s.2.2.1 inputs ys).mpr (by
      funext i
      simp [hiddenTuple, shifted, s.2.1.2 i, s.2.2.2 i])
  left_inv p := by
    cases p with
    | mk p hp =>
      cases p with
      | mk π₁ π₂ =>
        apply Subtype.ext
        rfl
  right_inv s := by
    cases s with
    | mk a fibers =>
      cases a with
      | mk a ha =>
        cases fibers with
        | mk f₁ f₂ =>
          cases f₁ with
          | mk π₁ hπ₁ =>
            cases f₂ with
            | mk π₂ hπ₂ =>
              have hhidden : hiddenTuple (q := q) π₁ inputs = a := by
                funext i
                exact hπ₁ i
              subst a
              simp [hiddenTuple]

/-- Real XoP output fibers have the compatible hidden-state count times two permutation fibers. -/
theorem real_xop_output_fiber_count
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs) :
    Fintype.card (outputFiber (G := G) (q := q) inputs ys) =
      compatibleCountNat ys *
        ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
  calc
    Fintype.card (outputFiber (G := G) (q := q) inputs ys)
        = Fintype.card (Sigma (fun a : compatibleFiber (G := G) (q := q) ys =>
            permFiber (G := G) (q := q) inputs a.1 ×
              permFiber (G := G) (q := q) inputs (shifted ys a.1))) := by
          exact Fintype.card_congr
            (outputFiberEquivCompatibleSigma (G := G) (q := q) inputs ys hinputs)
    _ = ∑ a : compatibleFiber (G := G) (q := q) ys,
          Fintype.card (permFiber (G := G) (q := q) inputs a.1 ×
            permFiber (G := G) (q := q) inputs (shifted ys a.1)) := by
          rw [Fintype.card_sigma]
    _ = ∑ _a : compatibleFiber (G := G) (q := q) ys,
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Fintype.card_prod]
          rw [namedPermFiber_card (G := G) (q := q) inputs hinputs a.1 a.2.1]
          rw [namedPermFiber_card (G := G) (q := q) inputs hinputs (shifted ys a.1) a.2.2]
    _ = Fintype.card (compatibleFiber (G := G) (q := q) ys) *
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
          simp [Finset.sum_const]
    _ = compatibleCountNat ys *
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
          rw [compatibleFiber_card_named]

/-- Real XoP output probabilities are the real output-fiber count divided by
the number of permutation pairs. -/
theorem real_xop_outputDist_apply
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs) :
    (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist) ys =
      (((compatibleCountNat ys *
        ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) : Nat) :
          Real) /
        (Fintype.card (Equiv.Perm G × Equiv.Perm G) : Real)) := by
  rw [xopReal_outputDist_eq_pair_pushforward]
  rw [Dist.fTransform_uniform_apply]
  have hfilter :
      ((Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
          (fun p => outputMap inputs (xopDDS (q := q) p.1 p.2) = ys)).card =
        compatibleCountNat ys *
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
    rw [← real_xop_output_fiber_count (G := G) (q := q) inputs ys hinputs]
    rw [← Fintype.card_subtype
      (p := fun p : Equiv.Perm G × Equiv.Perm G =>
        outputMap inputs (xopDDS (q := q) p.1 p.2) = ys)]
    rfl
  rw [hfilter]

/-- Real output probabilities with the permutation-pair denominator written as
`(|G|!)^2`. -/
theorem real_xop_outputDist_apply_factorial
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs) :
    (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist) ys =
      (((compatibleCountNat ys *
        ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) : Nat) :
          Real) /
        (((Fintype.card G).factorial * (Fintype.card G).factorial : Nat) : Real)) := by
  rw [real_xop_outputDist_apply (G := G) (q := q) inputs ys hinputs]
  rw [Fintype.card_prod, Fintype.card_perm]

/-- Real output probabilities normalized by the falling-factorial square
`(N)_q^2`. -/
theorem real_xop_outputDist_apply_descFactorial
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist) ys =
      (compatibleCountNNReal ys : Real) /
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          Real) := by
  rw [real_xop_outputDist_apply_factorial (G := G) (q := q) inputs ys hinputs]
  rw [compatibleCountNNReal_eq_coe_nat]
  norm_num [Nat.cast_mul]
  have hfact_nat :
      (Fintype.card G - q).factorial * (Fintype.card G).descFactorial q =
        (Fintype.card G).factorial :=
    Nat.factorial_mul_descFactorial hq
  have hfact :
      (((Fintype.card G - q).factorial : Nat) : Real) *
          (((Fintype.card G).descFactorial q : Nat) : Real) =
        (((Fintype.card G).factorial : Nat) : Real) := by
    exact_mod_cast hfact_nat
  have hf : (((Fintype.card G - q).factorial : Nat) : Real) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card G - q)
  rw [← hfact]
  field_simp [hf]

/-- The real fixed-input output-vector law is the SoP compatible-count visible
law. -/
theorem real_xop_outputDist_eq_sop_realVisibleDist
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist =
      SoP.realVisibleDist (G := G) (q := q) := by
  ext ys
  rw [real_xop_outputDist_apply_descFactorial (G := G) (q := q) inputs ys hinputs hq]
  rw [SoP.realVisibleDist_apply]
  rfl

/-- Real XoP fixed-output laws are invariant under replacing one injective
input tuple by another. -/
theorem xopReal_outputDist_eq_of_injective_inputs
    (inputs inputs' : Fin q → G)
    (hinputs : Function.Injective inputs) (hinputs' : Function.Injective inputs')
    (hq : q ≤ Fintype.card G) :
    Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist =
      Dist.fTransform (outputMap inputs') (xopRealPDS (G := G) (q := q)).dist := by
  rw [real_xop_outputDist_eq_sop_realVisibleDist (G := G) (q := q) inputs hinputs hq]
  rw [real_xop_outputDist_eq_sop_realVisibleDist (G := G) (q := q) inputs' hinputs' hq]

/-- Projecting the `q`-coordinate real visible law along an injective coordinate
map gives the lower-dimensional real visible law. -/
theorem realVisibleDist_project_eq_realVisibleDist
    {r : Nat} [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (idx : Fin r → Fin q) (hidx : Function.Injective idx)
    (hq : q ≤ Fintype.card G) :
    Dist.fTransform (fun y : Fin q → G => fun i : Fin r => y (idx i))
        (SoP.realVisibleDist (G := G) (q := q)) =
      SoP.realVisibleDist (G := G) (q := r) := by
  rw [← real_xop_outputDist_eq_sop_realVisibleDist (G := G) (q := q) inputs hinputs hq]
  let inputsR : Fin r → G := fun i => inputs (idx i)
  have hinputsR : Function.Injective inputsR := hinputs.comp hidx
  have hrq : r ≤ q := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective idx hidx
  have hr : r ≤ Fintype.card G := le_trans hrq hq
  rw [← real_xop_outputDist_eq_sop_realVisibleDist (G := G) (q := r) inputsR hinputsR hr]
  rw [xopReal_outputDist_eq_pair_pushforward (G := G) (q := q) inputs]
  rw [xopReal_outputDist_eq_pair_pushforward (G := G) (q := r) inputsR]
  rw [Dist.fTransform_comp]
  congr 1

/-- Real XoP fixed-input transcript probabilities at embedded transcripts are
the corresponding output-vector probabilities. -/
theorem real_xop_transcriptDist_transcriptEmbed_apply
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys) =
      (((compatibleCountNat ys *
        ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) : Nat) :
          Real) /
        (Fintype.card (Equiv.Perm G × Equiv.Perm G) : Real)) := by
  rw [transcriptDist_eq_output_pushforward]
  rw [fTransform_injective_apply]
  · exact real_xop_outputDist_apply (G := G) (q := q) inputs ys hinputs
  · exact transcriptEmbed_injective inputs

/-- Real embedded-transcript probabilities normalized by `(N)_q^2`. -/
theorem real_xop_transcriptDist_transcriptEmbed_apply_descFactorial
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys) =
      (compatibleCountNNReal ys : Real) /
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          Real) := by
  rw [transcriptDist_eq_output_pushforward]
  rw [fTransform_injective_apply]
  · exact real_xop_outputDist_apply_descFactorial (G := G) (q := q) inputs ys hinputs hq
  · exact transcriptEmbed_injective inputs

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Output-vector extraction from a stateless DDS is ordinary function evaluation. -/
theorem outputMap_ofFunq (inputs : Fin q → G) (f : G → G) :
    outputMap inputs (DDS.ofFunq (q := q) f) = fun i => f (inputs i) := by
  funext i
  simp [outputMap, DDS.ofFunq]

omit [AddGroup G] in
/--
The ideal XoP system induces the uniform output-vector distribution on
injective fixed inputs.  This reuses the shared `eval_nonces_uniform` lemma.
-/
theorem xopIdeal_output_uniform [Nonempty G]
    (inputs : Fin q → G) (h_inj : Function.Injective inputs) :
    Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist =
      Dist.uniform (Fin q → G) := by
  simp [xopIdealPDS, Instances.URFfun, Instances.URFfunOf]
  rw [Dist.fTransform_comp]
  have h_eval :
      (fun f : G → G => outputMap inputs (DDS.ofFunq (q := q) f)) =
        (fun f : G → G => fun i : Fin q => f (inputs i)) := by
    funext f i
    simp [outputMap, DDS.ofFunq]
  simpa [h_eval] using (Instances.eval_nonces_uniform (X := G) (Y := G) (n := q) inputs h_inj)

omit [AddGroup G] in
/-- The ideal fixed-input output-vector law is the SoP ideal visible law. -/
theorem xopIdeal_outputDist_eq_sop_idealVisibleDist [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs) :
    Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist =
      SoP.idealVisibleDist (G := G) (q := q) := by
  rw [xopIdeal_output_uniform inputs hinputs]
  rfl

omit [AddGroup G] in
/-- Ideal fixed-output laws are invariant under replacing one injective input
tuple by another. -/
theorem xopIdeal_outputDist_eq_of_injective_inputs [Nonempty G]
    (inputs inputs' : Fin q → G)
    (hinputs : Function.Injective inputs) (hinputs' : Function.Injective inputs') :
    Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist =
      Dist.fTransform (outputMap inputs') (xopIdealPDS (G := G) (q := q)).dist := by
  rw [xopIdeal_outputDist_eq_sop_idealVisibleDist (G := G) (q := q) inputs hinputs]
  rw [xopIdeal_outputDist_eq_sop_idealVisibleDist (G := G) (q := q) inputs' hinputs']

omit [AddGroup G] in
/-- Ideal XoP transcript distribution as uniform output vectors embedded into transcripts. -/
theorem xopIdeal_transcriptDist_eq_uniform_outputs [Nonempty G]
    (inputs : Fin q → G) (h_inj : Function.Injective inputs) :
    (xopIdealPDS (G := G) (q := q)).transcriptDist inputs =
      Dist.fTransform (transcriptEmbed inputs) (Dist.uniform (Fin q → G)) := by
  simp [PDS.transcriptDist, transcript_factors]
  rw [← Dist.fTransform_comp (g := transcriptEmbed inputs) (f := outputMap inputs)
    (X := (xopIdealPDS (G := G) (q := q)).dist)]
  rw [xopIdeal_output_uniform inputs h_inj]

/-- For injective fixed inputs, XoP transcript statistical distance is exactly
the SoP visible-output statistical distance. -/
theorem statDist_xop_transcriptDist_eq_sop_visibleStatDist [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    statDist
        ((xopRealPDS (G := G) (q := q)).transcriptDist inputs)
        ((xopIdealPDS (G := G) (q := q)).transcriptDist inputs) =
      SoP.visibleStatDist (G := G) (q := q) := by
  rw [transcriptDist_eq_output_pushforward]
  rw [xopIdeal_transcriptDist_eq_uniform_outputs inputs hinputs]
  rw [real_xop_outputDist_eq_sop_realVisibleDist (G := G) (q := q) inputs hinputs hq]
  rw [show Dist.uniform (Fin q → G) = SoP.idealVisibleDist (G := G) (q := q) from rfl]
  rw [statDist_fTransform_injective]
  · rfl
  · exact transcriptEmbed_injective inputs

/-- The restricted nonadaptive XoP advantage over injective inputs is exactly
the SoP visible-output statistical distance. -/
theorem xop_advantageOn_injective_eq_sop_visibleStatDist [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    advantageOn (xopRealPDS (G := G) (q := q)) (xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) =
      SoP.visibleStatDist (G := G) (q := q) := by
  classical
  let S : Finset (Fin q → G) :=
    Finset.univ.filter (InjectiveInputs (X := G) (q := q))
  have hnonempty : S.Nonempty := by
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    exact ⟨emb, by simp [S, InjectiveInputs, Function.Embedding.injective]⟩
  unfold advantageOn
  calc
    Finset.sup (Finset.univ.filter (InjectiveInputs (X := G) (q := q)))
        (fun inputs =>
          (⟨statDist
              ((xopRealPDS (G := G) (q := q)).transcriptDist inputs)
              ((xopIdealPDS (G := G) (q := q)).transcriptDist inputs),
            statDist_nonneg _ _⟩ : NNReal))
      = Finset.sup S (fun _ => SoP.visibleStatDist (G := G) (q := q)) := by
          apply Finset.sup_congr
          · rfl
          · intro inputs hmem
            have hinputs : Function.Injective inputs := by
              simpa [S, InjectiveInputs] using (Finset.mem_filter.mp hmem).2
            apply NNReal.coe_injective
            exact statDist_xop_transcriptDist_eq_sop_visibleStatDist
              (G := G) (q := q) inputs hinputs hq
    _ = SoP.visibleStatDist (G := G) (q := q) := by
          exact Finset.sup_const hnonempty _

/-- The exact visible SoP/orbit distance is a lower bound on the unrestricted
adaptive XoP advantage.

The reverse inequality is the remaining XoP-specific adaptive symmetry
argument: adaptive strategies should not beat the fixed-injective transcript
law because the concrete XoP and URF systems are input-name symmetric. -/
theorem sop_visibleStatDist_le_xop_adaptiveAdvantage [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    SoP.visibleStatDist (G := G) (q := q) ≤
      advantageAdaptive (xopRealPDS (G := G) (q := q))
        (xopIdealPDS (G := G) (q := q)) := by
  rw [← xop_advantageOn_injective_eq_sop_visibleStatDist (G := G) (q := q) hq]
  calc
    advantageOn (xopRealPDS (G := G) (q := q)) (xopIdealPDS (G := G) (q := q))
        (InjectiveInputs (X := G) (q := q))
        ≤ advantage (xopRealPDS (G := G) (q := q))
            (xopIdealPDS (G := G) (q := q)) := by
          exact advantageOn_le_advantage _ _ _
    _ ≤ advantageAdaptive (xopRealPDS (G := G) (q := q))
        (xopIdealPDS (G := G) (q := q)) := by
          exact advantage_le_advantageAdaptive _ _

/-- Real XoP assigns zero adaptive transcript mass to repeat-inconsistent
transcripts. -/
theorem xopReal_adaptiveTranscriptDist_eq_zero_of_not_repeatConsistent
    (e : DDE G G q) (t : Transcript G G q)
    (hnot : ¬ Transcript.RepeatConsistent t) :
    (xopRealPDS (G := G) (q := q)).adaptiveTranscriptDist e t = 0 := by
  unfold xopRealPDS xopDDS
  exact PDS.adaptiveTranscriptDist_statelessPDS_eq_zero_of_not_repeatConsistent
    (q := q)
    (D := Dist.uniform (Equiv.Perm G × Equiv.Perm G))
    (oracle := fun p : Equiv.Perm G × Equiv.Perm G => fun x : G => -p.1 x + p.2 x)
    e t hnot

omit [AddGroup G] in
/-- Ideal XoP/URFfun assigns zero adaptive transcript mass to
repeat-inconsistent transcripts. -/
theorem xopIdeal_adaptiveTranscriptDist_eq_zero_of_not_repeatConsistent [Nonempty G]
    (e : DDE G G q) (t : Transcript G G q)
    (hnot : ¬ Transcript.RepeatConsistent t) :
    (xopIdealPDS (G := G) (q := q)).adaptiveTranscriptDist e t = 0 := by
  unfold xopIdealPDS Instances.URFfun Instances.URFfunOf
  exact PDS.adaptiveTranscriptDist_statelessPDS_eq_zero_of_not_repeatConsistent
    (q := q)
    (D := Dist.uniform (G → G))
    (oracle := fun f : G → G => f)
    e t hnot

/-- On followed, repeat-consistent paths, real XoP adaptive point masses reduce
to the nonadaptive point mass of the transcript's fresh subtranscript. -/
theorem xopReal_adaptiveTranscriptDist_eq_fresh_transcriptDist
    (e : DDE G G q) (t : Transcript G G q)
    (hfollow : DDE.FollowsTranscript e t) (hrep : Transcript.RepeatConsistent t) :
    (xopRealPDS (G := G) (q := q)).adaptiveTranscriptDist e t =
      (xopRealPDS (G := G) (q := Fintype.card (Transcript.FreshPos t))).transcriptDist
        (Transcript.freshInputsFin t)
        (transcriptEmbed (G := G) (q := Fintype.card (Transcript.FreshPos t))
          (Transcript.freshInputsFin t) (Transcript.freshOutputsFin t)) := by
  unfold xopRealPDS xopDDS
  exact PDS.stateless_adaptiveTranscriptDist_eq_fresh_transcriptDist
    (q := q)
    (D := Dist.uniform (Equiv.Perm G × Equiv.Perm G))
    (oracle := fun p : Equiv.Perm G × Equiv.Perm G => fun x : G => -p.1 x + p.2 x)
    e t hfollow hrep

omit [AddGroup G] in
/-- On followed, repeat-consistent paths, ideal XoP/URF adaptive point masses
reduce to the nonadaptive point mass of the transcript's fresh subtranscript. -/
theorem xopIdeal_adaptiveTranscriptDist_eq_fresh_transcriptDist [Nonempty G]
    (e : DDE G G q) (t : Transcript G G q)
    (hfollow : DDE.FollowsTranscript e t) (hrep : Transcript.RepeatConsistent t) :
    (xopIdealPDS (G := G) (q := q)).adaptiveTranscriptDist e t =
      (xopIdealPDS (G := G) (q := Fintype.card (Transcript.FreshPos t))).transcriptDist
        (Transcript.freshInputsFin t)
        (transcriptEmbed (G := G) (q := Fintype.card (Transcript.FreshPos t))
          (Transcript.freshInputsFin t) (Transcript.freshOutputsFin t)) := by
  unfold xopIdealPDS Instances.URFfun Instances.URFfunOf
  exact PDS.stateless_adaptiveTranscriptDist_eq_fresh_transcriptDist
    (q := q)
    (D := Dist.uniform (G → G))
    (oracle := fun f : G → G => f)
    e t hfollow hrep

/-- Real XoP adaptive output histories are the pushforward of the uniform
permutation-pair distribution through the adaptive oracle-output map. -/
theorem xopReal_adaptiveOutputDist_eq_pair_pushforward
    (e : DDE G G q) :
    (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e =
      Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          DDE.outputHistoryOfOracle e (fun x : G => -p.1 x + p.2 x))
        (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) := by
  unfold xopRealPDS xopDDS
  exact PDS.stateless_adaptiveOutputDist_eq_oracle_pushforward
    (q := q)
    (D := Dist.uniform (Equiv.Perm G × Equiv.Perm G))
    (oracle := fun p : Equiv.Perm G × Equiv.Perm G => fun x : G => -p.1 x + p.2 x)
    e

omit [AddGroup G] in
/-- Ideal XoP/URF adaptive output histories are the pushforward of the uniform
function distribution through the adaptive oracle-output map. -/
theorem xopIdeal_adaptiveOutputDist_eq_fun_pushforward [Nonempty G]
    (e : DDE G G q) :
    (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e =
      Dist.fTransform (fun f : G → G => DDE.outputHistoryOfOracle e f)
        (Dist.uniform (G → G)) := by
  unfold xopIdealPDS Instances.URFfun Instances.URFfunOf
  exact PDS.stateless_adaptiveOutputDist_eq_oracle_pushforward
    (q := q)
    (D := Dist.uniform (G → G))
    (oracle := fun f : G → G => f)
    e

/-- For concrete XoP versus URF, adaptive transcript distance is exactly
adaptive output-history distance. -/
theorem statDist_xop_adaptiveTranscriptDist_eq_adaptiveOutputDist [Nonempty G]
    (e : DDE G G q) :
    statDist
        ((xopRealPDS (G := G) (q := q)).adaptiveTranscriptDist e)
        ((xopIdealPDS (G := G) (q := q)).adaptiveTranscriptDist e) =
      statDist
        ((xopRealPDS (G := G) (q := q)).adaptiveOutputDist e)
        ((xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e) := by
  exact statDist_adaptiveTranscriptDist_eq_adaptiveOutputDist
    (xopRealPDS (G := G) (q := q)) (xopIdealPDS (G := G) (q := q)) e

/-- The fixed-input XoP distance on the fresh part of any transcript is exactly
the SoP visible distance at the number of fresh input names.

This is the typed bridge from arbitrary adaptive transcripts back to the
existing injective fixed-input orbit law. -/
theorem statDist_xop_freshTranscriptDist_eq_sop_visibleStatDist [Nonempty G]
    (t : Transcript G G q) :
    statDist
        ((xopRealPDS (G := G) (q := Fintype.card (Transcript.FreshPos t))).transcriptDist
          (Transcript.freshInputsFin t))
        ((xopIdealPDS (G := G) (q := Fintype.card (Transcript.FreshPos t))).transcriptDist
          (Transcript.freshInputsFin t)) =
      SoP.visibleStatDist (G := G) (q := Fintype.card (Transcript.FreshPos t)) := by
  exact statDist_xop_transcriptDist_eq_sop_visibleStatDist
    (G := G)
    (q := Fintype.card (Transcript.FreshPos t))
    (Transcript.freshInputsFin t)
    (Transcript.freshInputsFin_injective t)
    (Transcript.freshPos_card_le_input t)

/-- Real XoP point mass at the fixed fresh transcript extracted from an
adaptive transcript. -/
theorem xopReal_freshTranscriptDist_transcriptEmbed_apply [Nonempty G]
    (t : Transcript G G q) :
    (xopRealPDS (G := G) (q := Fintype.card (Transcript.FreshPos t))).transcriptDist
        (Transcript.freshInputsFin t)
        (transcriptEmbed (G := G) (q := Fintype.card (Transcript.FreshPos t))
          (Transcript.freshInputsFin t) (Transcript.freshOutputsFin t)) =
      (compatibleCountNNReal (Transcript.freshOutputsFin t) : Real) /
        ((((Fintype.card G).descFactorial (Fintype.card (Transcript.FreshPos t)) *
            (Fintype.card G).descFactorial (Fintype.card (Transcript.FreshPos t)) : Nat) :
          Real)) := by
  exact real_xop_transcriptDist_transcriptEmbed_apply_descFactorial
    (G := G)
    (q := Fintype.card (Transcript.FreshPos t))
    (Transcript.freshInputsFin t)
    (Transcript.freshOutputsFin t)
    (Transcript.freshInputsFin_injective t)
    (Transcript.freshPos_card_le_input t)

omit [AddGroup G] in
/-- Ideal fixed-input transcript probabilities at embedded transcripts are uniform. -/
theorem xopIdeal_transcriptDist_transcriptEmbed_apply [Nonempty G]
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs) :
    (xopIdealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys) =
      (1 : Real) / (Fintype.card (Fin q → G) : Real) := by
  rw [xopIdeal_transcriptDist_eq_uniform_outputs inputs hinputs]
  rw [fTransform_injective_apply]
  · exact Dist.uniform_apply ys
  · exact transcriptEmbed_injective inputs

omit [AddGroup G] in
/-- Ideal XoP/URFfun point mass at the fixed fresh transcript extracted from an
adaptive transcript. -/
theorem xopIdeal_freshTranscriptDist_transcriptEmbed_apply [Nonempty G]
    (t : Transcript G G q) :
    (xopIdealPDS (G := G) (q := Fintype.card (Transcript.FreshPos t))).transcriptDist
        (Transcript.freshInputsFin t)
        (transcriptEmbed (G := G) (q := Fintype.card (Transcript.FreshPos t))
          (Transcript.freshInputsFin t) (Transcript.freshOutputsFin t)) =
      (1 : Real) / (Fintype.card (Fin (Fintype.card (Transcript.FreshPos t)) → G) :
        Real) := by
  exact xopIdeal_transcriptDist_transcriptEmbed_apply
    (G := G)
    (q := Fintype.card (Transcript.FreshPos t))
    (Transcript.freshInputsFin t)
    (Transcript.freshOutputsFin t)
    (Transcript.freshInputsFin_injective t)

/-- Real XoP adaptive point mass on a followed, repeat-consistent transcript,
written only in terms of the transcript's fresh output tuple. -/
theorem xopReal_adaptiveTranscriptDist_apply_of_follows_repeatConsistent [Nonempty G]
    (e : DDE G G q) (t : Transcript G G q)
    (hfollow : DDE.FollowsTranscript e t) (hrep : Transcript.RepeatConsistent t) :
    (xopRealPDS (G := G) (q := q)).adaptiveTranscriptDist e t =
      (compatibleCountNNReal (Transcript.freshOutputsFin t) : Real) /
        ((((Fintype.card G).descFactorial (Fintype.card (Transcript.FreshPos t)) *
            (Fintype.card G).descFactorial (Fintype.card (Transcript.FreshPos t)) : Nat) :
          Real)) := by
  rw [xopReal_adaptiveTranscriptDist_eq_fresh_transcriptDist
    (G := G) (q := q) e t hfollow hrep]
  exact xopReal_freshTranscriptDist_transcriptEmbed_apply (G := G) (q := q) t

omit [AddGroup G] in
/-- Ideal XoP/URFfun adaptive point mass on a followed, repeat-consistent
transcript, written only in terms of the number of fresh input names. -/
theorem xopIdeal_adaptiveTranscriptDist_apply_of_follows_repeatConsistent [Nonempty G]
    (e : DDE G G q) (t : Transcript G G q)
    (hfollow : DDE.FollowsTranscript e t) (hrep : Transcript.RepeatConsistent t) :
    (xopIdealPDS (G := G) (q := q)).adaptiveTranscriptDist e t =
      (1 : Real) / (Fintype.card (Fin (Fintype.card (Transcript.FreshPos t)) → G) :
        Real) := by
  rw [xopIdeal_adaptiveTranscriptDist_eq_fresh_transcriptDist
    (G := G) (q := q) e t hfollow hrep]
  exact xopIdeal_freshTranscriptDist_transcriptEmbed_apply (G := G) (q := q) t

/-- Real XoP adaptive output-history point mass for repeat-consistent replayed
transcripts. -/
theorem xopReal_adaptiveOutputDist_apply_of_replay_repeatConsistent [Nonempty G]
    (e : DDE G G q) (ys : Fin q → G)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)) :
    (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e ys =
      (compatibleCountNNReal
          (Transcript.freshOutputsFin (DDE.transcriptOfOutputs e ys)) : Real) /
        ((((Fintype.card G).descFactorial
              (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) *
            (Fintype.card G).descFactorial
              (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) : Nat) :
          Real)) := by
  rw [PDS.adaptiveOutputDist_apply_eq_adaptiveTranscriptDist_replay]
  exact xopReal_adaptiveTranscriptDist_apply_of_follows_repeatConsistent
    (G := G) (q := q) e (DDE.transcriptOfOutputs e ys)
    (DDE.followsTranscript_transcriptOfOutputs e ys) hrep

/-- Real XoP assigns zero adaptive output-history mass when replaying the output
history through the environment gives a repeat-inconsistent transcript. -/
theorem xopReal_adaptiveOutputDist_eq_zero_of_replay_not_repeatConsistent
    (e : DDE G G q) (ys : Fin q → G)
    (hnot : ¬ Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)) :
    (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e ys = 0 := by
  rw [PDS.adaptiveOutputDist_apply_eq_adaptiveTranscriptDist_replay]
  exact xopReal_adaptiveTranscriptDist_eq_zero_of_not_repeatConsistent
    (G := G) (q := q) e (DDE.transcriptOfOutputs e ys) hnot

/-- Pushing the real fixed-input visible law through an adaptive replay map gives
the same point mass as real XoP on repeat-consistent replayed histories. -/
theorem xopReal_positionTape_apply_of_replay_repeatConsistent [Nonempty G]
    (e : DDE G G q) (ys : Fin q → G) (hq : q ≤ Fintype.card G)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)) :
    (Dist.fTransform (DDE.outputHistoryOfPositionTape e)
        (SoP.realVisibleDist (G := G) (q := q))) ys =
      (compatibleCountNNReal
          (Transcript.freshOutputsFin (DDE.transcriptOfOutputs e ys)) : Real) /
        (((Fintype.card G).descFactorial
              (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) *
            (Fintype.card G).descFactorial
              (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) : Nat) :
          Real) := by
  let t := DDE.transcriptOfOutputs e ys
  let r := Fintype.card (Transcript.FreshPos t)
  let idx : Fin r → Fin q :=
    fun k => ((Fintype.equivFin (Transcript.FreshPos t)).symm k).1
  have hidx : Function.Injective idx := by
    intro a b h
    apply (Fintype.equivFin (Transcript.FreshPos t)).symm.injective
    apply Subtype.ext
    exact h
  rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
      (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
  let inputs : Fin q → G := fun i => emb i
  have hinputs : Function.Injective inputs := emb.injective
  have hproj := realVisibleDist_project_eq_realVisibleDist
    (G := G) (q := q) (r := r) inputs hinputs idx hidx hq
  have hmass :=
    congrArg (fun D : Dist (Fin r → G) => D (Transcript.freshOutputsFin t)) hproj
  change (Dist.fTransform (fun y : Fin q → G => fun i : Fin r => y (idx i))
      (SoP.realVisibleDist (G := G) (q := q))) (Transcript.freshOutputsFin t) =
    SoP.realVisibleDist (G := G) (q := r) (Transcript.freshOutputsFin t) at hmass
  rw [SoP.realVisibleDist_apply] at hmass
  rw [SoP.realVisibleMass_eq] at hmass
  have hmass_real :
      (Dist.fTransform (fun y : Fin q → G => fun i : Fin r => y (idx i))
          (SoP.realVisibleDist (G := G) (q := q))) (Transcript.freshOutputsFin t) =
        (compatibleCountNNReal (Transcript.freshOutputsFin t) : Real) /
          (((Fintype.card G).descFactorial r *
            (Fintype.card G).descFactorial r : Nat) : Real) := by
    simpa only [NNReal.coe_div, NNReal.coe_natCast] using hmass
  rw [← hmass_real]
  rw [Dist.fTransform_apply_eq_sum]
  rw [Dist.fTransform_apply_eq_sum]
  rw [show
    (Finset.univ.filter (fun y : Fin q → G => DDE.outputHistoryOfPositionTape e y = ys)) =
      (Finset.univ.filter
        (fun y : Fin q → G =>
          (fun i : Fin r => y (idx i)) = Transcript.freshOutputsFin t)) from by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [DDE.outputHistoryOfPositionTape_eq_iff_fresh_values (q := q) e ys y hrep]
      change (∀ i : Fin q, Transcript.FreshAt t i → y i = ys i) ↔
        (fun i : Fin r => y (idx i)) = Transcript.freshOutputsFin t
      constructor
      · intro h
        apply (Transcript.fresh_values_iff_project_eq (q := q) t y).1
        intro i hi
        simpa [t, DDE.transcriptOfOutputs] using h i hi
      · intro h i hi
        have hval := (Transcript.fresh_values_iff_project_eq (q := q) t y).2 h i hi
        simpa [t, DDE.transcriptOfOutputs] using hval]

omit [AddGroup G] in
/-- Ideal XoP/URFfun adaptive output-history point mass for repeat-consistent
replayed transcripts. -/
theorem xopIdeal_adaptiveOutputDist_apply_of_replay_repeatConsistent [Nonempty G]
    (e : DDE G G q) (ys : Fin q → G)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)) :
    (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e ys =
      (1 : Real) /
        (Fintype.card
          (Fin (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) → G) :
        Real) := by
  rw [PDS.adaptiveOutputDist_apply_eq_adaptiveTranscriptDist_replay]
  exact xopIdeal_adaptiveTranscriptDist_apply_of_follows_repeatConsistent
    (G := G) (q := q) e (DDE.transcriptOfOutputs e ys)
    (DDE.followsTranscript_transcriptOfOutputs e ys) hrep

omit [AddGroup G] in
/-- Ideal XoP/URFfun assigns zero adaptive output-history mass when replaying
the output history through the environment gives a repeat-inconsistent
transcript. -/
theorem xopIdeal_adaptiveOutputDist_eq_zero_of_replay_not_repeatConsistent [Nonempty G]
    (e : DDE G G q) (ys : Fin q → G)
    (hnot : ¬ Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)) :
    (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e ys = 0 := by
  rw [PDS.adaptiveOutputDist_apply_eq_adaptiveTranscriptDist_replay]
  exact xopIdeal_adaptiveTranscriptDist_eq_zero_of_not_repeatConsistent
    (G := G) (q := q) e (DDE.transcriptOfOutputs e ys) hnot

omit [AddGroup G] in
/-- The ideal/URF adaptive output-history law is the pushforward of a uniform
position tape through the deterministic replay map induced by the environment. -/
theorem xopIdeal_adaptiveOutputDist_eq_positionTape_uniform [Nonempty G]
    (e : DDE G G q) :
    (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e =
      Dist.fTransform (DDE.outputHistoryOfPositionTape e) (Dist.uniform (Fin q → G)) := by
  ext ys
  by_cases hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)
  · rw [xopIdeal_adaptiveOutputDist_apply_of_replay_repeatConsistent
      (G := G) (q := q) e ys hrep]
    rw [DDE.positionTape_uniform_apply_of_repeatConsistent (q := q) e ys hrep]
    rw [Fintype.card_fun, Fintype.card_fun]
    simp only [Fintype.card_fin, Nat.cast_pow]
    let t := DDE.transcriptOfOutputs e ys
    have hfresh_le : Fintype.card (Transcript.FreshPos t) ≤ q :=
      Transcript.freshPos_card_le_query t
    have hG : (Fintype.card G : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := G)).ne'
    rw [show (Fintype.card G : Real) ^ q =
        (Fintype.card G : Real) ^ (q - Fintype.card (Transcript.FreshPos t)) *
          (Fintype.card G : Real) ^ Fintype.card (Transcript.FreshPos t) from by
      rw [← pow_add, Nat.sub_add_cancel hfresh_le]]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hG), one_div]
  · rw [xopIdeal_adaptiveOutputDist_eq_zero_of_replay_not_repeatConsistent
      (G := G) (q := q) e ys hrep]
    rw [DDE.positionTape_uniform_apply_eq_zero_of_not_repeatConsistent (q := q) e ys hrep]

/-- The real/XoP adaptive output-history law is the pushforward of the fixed
real visible law through the deterministic replay map induced by the
environment. -/
theorem xopReal_adaptiveOutputDist_eq_positionTape_realVisible [Nonempty G]
    (e : DDE G G q) (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e =
      Dist.fTransform (DDE.outputHistoryOfPositionTape e)
        (SoP.realVisibleDist (G := G) (q := q)) := by
  ext ys
  by_cases hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)
  · rw [xopReal_adaptiveOutputDist_apply_of_replay_repeatConsistent
      (G := G) (q := q) e ys hrep]
    rw [xopReal_positionTape_apply_of_replay_repeatConsistent
      (G := G) (q := q) e ys hq hrep]
  · rw [xopReal_adaptiveOutputDist_eq_zero_of_replay_not_repeatConsistent
      (G := G) (q := q) e ys hrep]
    rw [DDE.positionTape_pushforward_apply_eq_zero_of_not_repeatConsistent
      (q := q) (SoP.realVisibleDist (G := G) (q := q)) e ys hrep]

/-- Real XoP is adaptively output-equivalent to the position-tape PDS whose
visible tape law is the block-uniform representative of the real visible law.

This is the LM20 representative shape at the output-history level: choose a
classifier block according to the real block mass, sample uniformly inside that
block, then replay the sampled tape through the environment. -/
theorem xopReal_adaptiveOutputDist_eq_positionTape_blockUniform
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      SoP.compatibleCountNNReal (G := G) (q := q) y =
        SoP.compatibleCountNNReal (G := G) (q := q) z)
    (e : DDE G G q) (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e =
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.realVisibleDist (G := G) (q := q)) κ)).adaptiveOutputDist e := by
  calc
    (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e =
        Dist.fTransform (DDE.outputHistoryOfPositionTape e)
          (SoP.realVisibleDist (G := G) (q := q)) := by
          exact xopReal_adaptiveOutputDist_eq_positionTape_realVisible
            (G := G) (q := q) e hq
    _ = Dist.fTransform (DDE.outputHistoryOfPositionTape e)
        (SoP.classifierBlockUniform
          (SoP.realVisibleDist (G := G) (q := q)) κ) := by
          exact congrArg (fun D : Dist (Fin q → G) =>
            Dist.fTransform (DDE.outputHistoryOfPositionTape e) D)
            (SoP.realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant
              (G := G) (q := q) κ hC)
    _ = (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.realVisibleDist (G := G) (q := q)) κ)).adaptiveOutputDist e := by
          exact (PDS.adaptiveOutputDist_ofPositionTapeDist_eq
            (q := q) (X := G)
            (SoP.classifierBlockUniform
              (SoP.realVisibleDist (G := G) (q := q)) κ) e).symm

omit [AddGroup G] in
/-- Ideal XoP/URF is adaptively output-equivalent to the position-tape PDS whose
visible tape law is the block-uniform representative of the ideal visible law. -/
theorem xopIdeal_adaptiveOutputDist_eq_positionTape_blockUniform
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) (e : DDE G G q) :
    (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e =
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.idealVisibleDist (G := G) (q := q)) κ)).adaptiveOutputDist e := by
  calc
    (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e =
        Dist.fTransform (DDE.outputHistoryOfPositionTape e)
          (SoP.idealVisibleDist (G := G) (q := q)) := by
          exact xopIdeal_adaptiveOutputDist_eq_positionTape_uniform (G := G) (q := q) e
    _ = Dist.fTransform (DDE.outputHistoryOfPositionTape e)
        (SoP.classifierBlockUniform
          (SoP.idealVisibleDist (G := G) (q := q)) κ) := by
          exact congrArg (fun D : Dist (Fin q → G) =>
            Dist.fTransform (DDE.outputHistoryOfPositionTape e) D)
            (SoP.idealVisibleDist_eq_classifierBlockUniform (G := G) (q := q) κ)
    _ = (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.idealVisibleDist (G := G) (q := q)) κ)).adaptiveOutputDist e := by
          exact (PDS.adaptiveOutputDist_ofPositionTapeDist_eq
            (q := q) (X := G)
            (SoP.classifierBlockUniform
              (SoP.idealVisibleDist (G := G) (q := q)) κ) e).symm

/-- On injective fixed inputs, real XoP has the same nonadaptive transcript
law as the position-tape PDS built from the real block-uniform visible
representative.  This is the nonadaptive representative equality that feeds the
generic LM20 adaptive/nonadaptive bridge. -/
theorem xopReal_transcriptDist_eq_positionTape_blockUniform_of_injective_inputs
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      SoP.compatibleCountNNReal (G := G) (q := q) y =
        SoP.compatibleCountNNReal (G := G) (q := q) z)
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs =
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.realVisibleDist (G := G) (q := q)) κ)).transcriptDist inputs := by
  rw [transcriptDist_eq_output_pushforward]
  rw [PDS.transcriptDist_ofPositionTapeDist_eq
    (D := SoP.classifierBlockUniform (SoP.realVisibleDist (G := G) (q := q)) κ)
    (inputs := inputs) hinputs]
  have houtput :
      Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist =
        SoP.realVisibleDist (G := G) (q := q) := by
    exact real_xop_outputDist_eq_sop_realVisibleDist
      (G := G) (q := q) inputs hinputs hq
  rw [houtput]
  exact congrArg
    (fun D : Dist (Fin q → G) => Dist.fTransform (Transcript.ofOutputs inputs) D)
    (SoP.realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant
      (G := G) (q := q) κ hC)

omit [AddGroup G] in
/-- On injective fixed inputs, ideal XoP/URF has the same nonadaptive
transcript law as the position-tape PDS built from the ideal block-uniform
visible representative. -/
theorem xopIdeal_transcriptDist_eq_positionTape_blockUniform_of_injective_inputs
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (inputs : Fin q → G) (hinputs : Function.Injective inputs) :
    (xopIdealPDS (G := G) (q := q)).transcriptDist inputs =
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.idealVisibleDist (G := G) (q := q)) κ)).transcriptDist inputs := by
  rw [xopIdeal_transcriptDist_eq_uniform_outputs inputs hinputs]
  rw [PDS.transcriptDist_ofPositionTapeDist_eq
    (D := SoP.classifierBlockUniform (SoP.idealVisibleDist (G := G) (q := q)) κ)
    (inputs := inputs) hinputs]
  exact congrArg
    (fun D : Dist (Fin q → G) => Dist.fTransform (Transcript.ofOutputs inputs) D)
    (SoP.idealVisibleDist_eq_classifierBlockUniform (G := G) (q := q) κ)

/-- Real XoP has the same nonadaptive transcript law as the real
block-uniform position-tape representative on every fixed input sequence.

This is the explicit nonadaptive equality used by the LM20 adaptive bridge.
It is stated for all input sequences, not only injective ones; repeats are
handled by the position-tape replay semantics. -/
theorem xopReal_transcriptDist_eq_positionTape_blockUniform
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      SoP.compatibleCountNNReal (G := G) (q := q) y =
        SoP.compatibleCountNNReal (G := G) (q := q) z)
    (inputs : Fin q → G) (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs =
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.realVisibleDist (G := G) (q := q)) κ)).transcriptDist inputs := by
  rw [← PDS.adaptiveTranscriptDist_nonadaptive
    (S := xopRealPDS (G := G) (q := q)) (inputs := inputs)]
  rw [← PDS.adaptiveTranscriptDist_nonadaptive
    (S := PDS.ofPositionTapeDist (q := q) (X := G)
      (SoP.classifierBlockUniform (SoP.realVisibleDist (G := G) (q := q)) κ))
    (inputs := inputs)]
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward
    (S := xopRealPDS (G := G) (q := q)) (e := DDE.nonadaptive inputs)]
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward
    (S := PDS.ofPositionTapeDist (q := q) (X := G)
      (SoP.classifierBlockUniform (SoP.realVisibleDist (G := G) (q := q)) κ))
    (e := DDE.nonadaptive inputs)]
  rw [xopReal_adaptiveOutputDist_eq_positionTape_blockUniform
    (G := G) (q := q) κ hC (DDE.nonadaptive inputs) hq]

omit [AddGroup G] in
/-- Ideal XoP/URF has the same nonadaptive transcript law as the ideal
block-uniform position-tape representative on every fixed input sequence. -/
theorem xopIdeal_transcriptDist_eq_positionTape_blockUniform
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (inputs : Fin q → G) :
    (xopIdealPDS (G := G) (q := q)).transcriptDist inputs =
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.idealVisibleDist (G := G) (q := q)) κ)).transcriptDist inputs := by
  rw [← PDS.adaptiveTranscriptDist_nonadaptive
    (S := xopIdealPDS (G := G) (q := q)) (inputs := inputs)]
  rw [← PDS.adaptiveTranscriptDist_nonadaptive
    (S := PDS.ofPositionTapeDist (q := q) (X := G)
      (SoP.classifierBlockUniform (SoP.idealVisibleDist (G := G) (q := q)) κ))
    (inputs := inputs)]
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward
    (S := xopIdealPDS (G := G) (q := q)) (e := DDE.nonadaptive inputs)]
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward
    (S := PDS.ofPositionTapeDist (q := q) (X := G)
      (SoP.classifierBlockUniform (SoP.idealVisibleDist (G := G) (q := q)) κ))
    (e := DDE.nonadaptive inputs)]
  rw [xopIdeal_adaptiveOutputDist_eq_positionTape_blockUniform
    (G := G) (q := q) κ (DDE.nonadaptive inputs)]

/-- Real XoP is LM20-equivalent to the honest position-tape PDS obtained from
the real block-uniform visible representative. -/
theorem xopReal_equivAdaptive_positionTape_blockUniform
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      SoP.compatibleCountNNReal (G := G) (q := q) y =
        SoP.compatibleCountNNReal (G := G) (q := q) z)
    (hq : q ≤ Fintype.card G) :
    PDS.equivAdaptive (xopRealPDS (G := G) (q := q))
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.realVisibleDist (G := G) (q := q)) κ)) := by
  exact PDS.equivAdaptive_of_transcriptDist_eq _ _
    (fun inputs =>
      xopReal_transcriptDist_eq_positionTape_blockUniform
        (G := G) (q := q) κ hC inputs hq)

omit [AddGroup G] in
/-- Ideal XoP/URF is LM20-equivalent to the honest position-tape PDS obtained
from the ideal block-uniform visible representative. -/
theorem xopIdeal_equivAdaptive_positionTape_blockUniform
    [Nonempty G] {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) :
    PDS.equivAdaptive (xopIdealPDS (G := G) (q := q))
      (PDS.ofPositionTapeDist (q := q) (X := G)
        (SoP.classifierBlockUniform
          (SoP.idealVisibleDist (G := G) (q := q)) κ)) := by
  exact PDS.equivAdaptive_of_transcriptDist_eq _ _
    (fun inputs =>
      xopIdeal_transcriptDist_eq_positionTape_blockUniform
        (G := G) (q := q) κ inputs)

local instance replayRepeatConsistentDecidable
    (e : DDE G G q) (ys : Fin q → G) :
    Decidable (Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)) := by
  unfold Transcript.RepeatConsistent
  infer_instance

/-- Exact adaptive output-history distance as a sum over replayed fresh
compatible-count deviations. -/
theorem statDist_xop_adaptiveOutputDist_eq_sum_replay_fresh [Nonempty G]
    (e : DDE G G q) :
    statDist
        ((xopRealPDS (G := G) (q := q)).adaptiveOutputDist e)
        ((xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e) =
      ∑ ys : Fin q → G,
        if _hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys) then
          max
            ((compatibleCountNNReal
                (Transcript.freshOutputsFin (DDE.transcriptOfOutputs e ys)) : Real) /
              ((((Fintype.card G).descFactorial
                    (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) *
                  (Fintype.card G).descFactorial
                    (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) : Nat) :
                Real)) -
            (1 : Real) /
              (Fintype.card
                (Fin (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) → G) :
              Real)) 0
        else
          0 := by
  -- the signed carrier indexes `statDist` by `(X - Y).support`, not `univ`
  rw [statDist_eq_sum_univ]
  apply Finset.sum_congr rfl
  intro ys _
  by_cases hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys)
  · rw [dif_pos hrep]
    rw [xopReal_adaptiveOutputDist_apply_of_replay_repeatConsistent
      (G := G) (q := q) e ys hrep]
    rw [xopIdeal_adaptiveOutputDist_apply_of_replay_repeatConsistent
      (G := G) (q := q) e ys hrep]
  · rw [dif_neg hrep]
    rw [xopReal_adaptiveOutputDist_eq_zero_of_replay_not_repeatConsistent
      (G := G) (q := q) e ys hrep]
    rw [xopIdeal_adaptiveOutputDist_eq_zero_of_replay_not_repeatConsistent
      (G := G) (q := q) e ys hrep]
    simp

/-- Exact adaptive transcript distance as a sum over replayed fresh
compatible-count deviations. -/
theorem statDist_xop_adaptiveTranscriptDist_eq_sum_replay_fresh [Nonempty G]
    (e : DDE G G q) :
    statDist
        ((xopRealPDS (G := G) (q := q)).adaptiveTranscriptDist e)
        ((xopIdealPDS (G := G) (q := q)).adaptiveTranscriptDist e) =
      ∑ ys : Fin q → G,
        if _hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e ys) then
          max
            ((compatibleCountNNReal
                (Transcript.freshOutputsFin (DDE.transcriptOfOutputs e ys)) : Real) /
              ((((Fintype.card G).descFactorial
                    (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) *
                  (Fintype.card G).descFactorial
                    (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) : Nat) :
                Real)) -
            (1 : Real) /
              (Fintype.card
                (Fin (Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e ys))) → G) :
              Real)) 0
        else
          0 := by
  rw [statDist_xop_adaptiveTranscriptDist_eq_adaptiveOutputDist (G := G) (q := q) e]
  exact statDist_xop_adaptiveOutputDist_eq_sum_replay_fresh (G := G) (q := q) e

/-- Fixed-input output-vector distance is the exact SoP visible distance. -/
theorem statDist_xop_outputDist_eq_sop_visibleStatDist [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    statDist
        (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist)
        (Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist) =
      SoP.visibleStatDist (G := G) (q := q) := by
  rw [← statDist_fTransform_injective
    (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist)
    (Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist)
    (transcriptEmbed inputs) (transcriptEmbed_injective inputs)]
  rw [← transcriptDist_eq_output_pushforward (G := G) (q := q)
    (xopRealPDS (G := G) (q := q)) inputs]
  rw [← transcriptDist_eq_output_pushforward (G := G) (q := q)
    (xopIdealPDS (G := G) (q := q)) inputs]
  exact statDist_xop_transcriptDist_eq_sop_visibleStatDist
    (G := G) (q := q) inputs hinputs hq

/-- Data-processing bridge for the remaining adaptive symmetry theorem.

If, for a fixed adaptive environment, both the real and ideal adaptive
output-history laws are obtained by applying the same deterministic map to the
fixed-input output-vector laws, then that environment's transcript distance is
bounded by the exact SoP visible/orbit distance. -/
theorem statDist_xop_adaptiveTranscriptDist_le_sop_visibleStatDist_of_output_pushforward
    [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G)
    (e : DDE G G q) (φ : (Fin q → G) → (Fin q → G))
    (hReal :
      (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e =
        Dist.fTransform φ
          (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist))
    (hIdeal :
      (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e =
        Dist.fTransform φ
          (Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist)) :
    statDist
        ((xopRealPDS (G := G) (q := q)).adaptiveTranscriptDist e)
        ((xopIdealPDS (G := G) (q := q)).adaptiveTranscriptDist e) ≤
      SoP.visibleStatDist (G := G) (q := q) := by
  rw [statDist_xop_adaptiveTranscriptDist_eq_adaptiveOutputDist (G := G) (q := q) e]
  rw [hReal, hIdeal]
  calc
    statDist
        (Dist.fTransform φ
          (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist))
        (Dist.fTransform φ
          (Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist))
        ≤ statDist
            (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist)
            (Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist) := by
          exact statDist_fTransform_le _ _ φ
    _ = SoP.visibleStatDist (G := G) (q := q) := by
          exact statDist_xop_outputDist_eq_sop_visibleStatDist
            (G := G) (q := q) inputs hinputs hq

/-- Conditional adaptive upper bound: it remains to prove that every adaptive
environment's output-history laws factor through the fixed distinct-input
output-vector laws by a common deterministic replay map. -/
theorem xop_adaptiveAdvantage_le_sop_visibleStatDist_of_output_pushforward
    [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G)
    (hpush : ∀ e : DDE G G q,
      ∃ φ : (Fin q → G) → (Fin q → G),
        (xopRealPDS (G := G) (q := q)).adaptiveOutputDist e =
          Dist.fTransform φ
            (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist) ∧
        (xopIdealPDS (G := G) (q := q)).adaptiveOutputDist e =
          Dist.fTransform φ
            (Dist.fTransform (outputMap inputs) (xopIdealPDS (G := G) (q := q)).dist)) :
    advantageAdaptive (xopRealPDS (G := G) (q := q))
        (xopIdealPDS (G := G) (q := q)) ≤
      SoP.visibleStatDist (G := G) (q := q) := by
  apply advantageAdaptive_le_of_pointwise
  intro e
  rcases hpush e with ⟨φ, hReal, hIdeal⟩
  exact statDist_xop_adaptiveTranscriptDist_le_sop_visibleStatDist_of_output_pushforward
    (G := G) (q := q) inputs hinputs hq e φ hReal hIdeal

/-- Adaptive XoP distinguishing advantage is bounded by the exact fixed-visible
SoP/orbit distance.

The proof factors every adaptive environment through the same deterministic
position-tape replay map on both sides, then applies data processing. -/
theorem xop_adaptiveAdvantage_le_sop_visibleStatDist [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (xopRealPDS (G := G) (q := q))
        (xopIdealPDS (G := G) (q := q)) ≤
      SoP.visibleStatDist (G := G) (q := q) := by
  apply xop_adaptiveAdvantage_le_sop_visibleStatDist_of_output_pushforward
    (G := G) (q := q) inputs hinputs hq
  intro e
  refine ⟨DDE.outputHistoryOfPositionTape e, ?_, ?_⟩
  · rw [xopReal_adaptiveOutputDist_eq_positionTape_realVisible
      (G := G) (q := q) e hq]
    rw [real_xop_outputDist_eq_sop_realVisibleDist
      (G := G) (q := q) inputs hinputs hq]
  · rw [xopIdeal_adaptiveOutputDist_eq_positionTape_uniform (G := G) (q := q) e]
    rw [xopIdeal_outputDist_eq_sop_idealVisibleDist (G := G) (q := q) inputs hinputs]
    rfl

/-- The unrestricted adaptive XoP advantage is exactly the fixed-visible
SoP/orbit distance. -/
theorem xop_adaptiveAdvantage_eq_sop_visibleStatDist [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (xopRealPDS (G := G) (q := q))
        (xopIdealPDS (G := G) (q := q)) =
      SoP.visibleStatDist (G := G) (q := q) := by
  rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
      (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
  apply le_antisymm
  · exact xop_adaptiveAdvantage_le_sop_visibleStatDist
      (G := G) (q := q) emb emb.injective hq
  · exact sop_visibleStatDist_le_xop_adaptiveAdvantage (G := G) (q := q) hq

omit [AddGroup G] in
/-- Positive-error sums under the ideal fixed-input transcript law reduce to
visible-output sums. -/
theorem positiveError_idealTranscript_eq_visible [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (density : Transcript G G q → NNReal) :
    (∑ t : Transcript G G q,
      max
        (density t * (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t -
          (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t) 0) =
      ∑ y : Fin q → G,
        max
          (density (transcriptEmbed inputs y) * (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0 := by
  rw [xopIdeal_transcriptDist_eq_uniform_outputs inputs hinputs]
  exact positiveError_transcriptEmbed_pushforward_eq_visible
    (G := G) (q := q) inputs density

/-- Positive-error sum for the corrected XoP compatible-count density, reduced
to visible output tuples. -/
theorem positiveError_xop_compatibleCount_eq_visible [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    (∑ t : Transcript G G q,
      max
        (((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density t) *
            (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t -
          (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t) 0) =
      ∑ y : Fin q → G,
        max
          (((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density
              (transcriptEmbed inputs y)) * (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0 := by
  exact positiveError_idealTranscript_eq_visible
    (G := G) (q := q) inputs hinputs
    ((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density)

omit [DecidableEq G] in
/-- The visible positive-error sum for the corrected compatible-count density
does not depend on the fixed input sequence. -/
theorem visiblePositiveError_xop_compatibleCount_eq_count [Nonempty G]
    (inputs : Fin q → G) (hq : q ≤ Fintype.card G) :
    (∑ y : Fin q → G,
        max
          (((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density
              (transcriptEmbed inputs y)) * (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0) =
      ∑ y : Fin q → G,
        max
          ((compatibleCountNNReal y /
              ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
                  NNReal) /
                (((Fintype.card G ^ q : Nat) : NNReal)))) *
            (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0 := by
  apply Finset.sum_congr rfl
  intro y _
  simp only [Counting.CompatibleCount.density,
    compatibleCountWithExpectationNormalizer_Z,
    compatibleCountWithExpectationNormalizer_normalizer]
  rw [transcriptOutputs_transcriptEmbed]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

/-- Embedded-transcript density identity using the corrected expectation
normalizer. -/
theorem real_eq_density_mul_ideal_transcriptEmbed [Nonempty G]
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys) =
      (compatibleTranscriptCountNNReal (transcriptEmbed inputs ys) /
          ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
              NNReal) /
            (Fintype.card (Fin q → G) : NNReal))) *
        ((xopIdealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys)) := by
  rw [real_xop_transcriptDist_transcriptEmbed_apply_descFactorial
    (G := G) (q := q) inputs ys hinputs hq]
  rw [xopIdeal_transcriptDist_transcriptEmbed_apply (G := G) (q := q) inputs ys hinputs]
  rw [compatibleTranscriptCountNNReal_transcriptEmbed]
  have hcard : (Fintype.card (Fin q → G) : NNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin q → G) ≠ 0)
  simp only [NNReal.coe_natCast]
  field_simp [hcard]

/-- Embedded-transcript density identity with the normalizer written as
`(N)_q^2 / N^q`. -/
theorem real_eq_density_mul_ideal_transcriptEmbed_descPow [Nonempty G]
    (inputs ys : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys) =
      (compatibleTranscriptCountNNReal (transcriptEmbed inputs ys) /
          ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
              NNReal) /
            (((Fintype.card G ^ q : Nat) : NNReal)))) *
        ((xopIdealPDS (G := G) (q := q)).transcriptDist inputs (transcriptEmbed inputs ys)) := by
  rw [real_eq_density_mul_ideal_transcriptEmbed (G := G) (q := q) inputs ys hinputs hq]
  rw [visibleTupleCount_eq_pow]

/-- Full fixed-input transcript density identity with the corrected normalizer
`(N)_q^2 / N^q`, for injective input sequences. -/
theorem real_eq_density_mul_ideal_transcript [Nonempty G]
    (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G) (t : Transcript G G q) :
    (xopRealPDS (G := G) (q := q)).transcriptDist inputs t =
      (compatibleTranscriptCountNNReal t /
          ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
              NNReal) /
            (((Fintype.card G ^ q : Nat) : NNReal)))) *
        ((xopIdealPDS (G := G) (q := q)).transcriptDist inputs t) := by
  by_cases h : t = transcriptEmbed inputs (Combinatorics.transcriptOutputs t)
  · rw [h]
    exact real_eq_density_mul_ideal_transcriptEmbed_descPow
      (G := G) (q := q) inputs (Combinatorics.transcriptOutputs t) hinputs hq
  · have hreal : (xopRealPDS (G := G) (q := q)).transcriptDist inputs t = 0 := by
      rw [transcriptDist_eq_output_pushforward]
      exact fTransform_transcriptEmbed_eq_zero_of_not_image
        (G := G) (q := q)
        (Dist.fTransform (outputMap inputs) (xopRealPDS (G := G) (q := q)).dist)
        inputs t h
    have hideal : (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t = 0 := by
      rw [xopIdeal_transcriptDist_eq_uniform_outputs inputs hinputs]
      exact fTransform_transcriptEmbed_eq_zero_of_not_image
        (G := G) (q := q) (Dist.uniform (Fin q → G)) inputs t h
    rw [hreal, hideal, mul_zero]

/-- The concrete corrected compatible-count package realizes the normalized
counting model once the analytic positive-error estimate is supplied. -/
theorem realizes_xop_compatibleCount_of_positiveError [Nonempty G]
    (ε : NNReal) (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G)
    (hpos :
      (∑ t : Transcript G G q,
        max
          ((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density t *
              (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t -
            (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t) 0) ≤ ε) :
    Nonempty
      (Counting.RealizesNormalizedCountingModel
        (real := (xopRealPDS (G := G) (q := q)).transcriptDist inputs)
        (reference := (xopIdealPDS (G := G) (q := q)).transcriptDist inputs)
        (ε := ε)
        (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq)) := by
  refine _root_.RandomSystems.Applications.XoP.Counting.realizesNormalizedCountingModel_of_density_and_positiveError
    (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq) ?_ hpos
  intro t
  exact real_eq_density_mul_ideal_transcript (G := G) (q := q) inputs hinputs hq t

/-- Visible-output analytic positive-error estimates are enough to realize the
concrete corrected normalized-counting model. -/
theorem realizes_xop_compatibleCount_of_visible_positiveError [Nonempty G]
    (ε : NNReal) (inputs : Fin q → G) (hinputs : Function.Injective inputs)
    (hq : q ≤ Fintype.card G)
    (hvisible :
      (∑ y : Fin q → G,
        max
          (((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density
              (transcriptEmbed inputs y)) * (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0) ≤ ε) :
    Nonempty
      (Counting.RealizesNormalizedCountingModel
        (real := (xopRealPDS (G := G) (q := q)).transcriptDist inputs)
        (reference := (xopIdealPDS (G := G) (q := q)).transcriptDist inputs)
        (ε := ε)
        (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq)) := by
  apply realizes_xop_compatibleCount_of_positiveError
    (G := G) (q := q) ε inputs hinputs hq
  rw [positiveError_xop_compatibleCount_eq_visible (G := G) (q := q) inputs hinputs hq]
  exact hvisible

/-- A visible-output positive-error estimate for every injective input sequence
implies the restricted non-adaptive XoP advantage bound. -/
theorem xop_advantageOn_injective_of_visible_positiveError
    [Nonempty G]
    (ε : NNReal)
    (hvisible : ∀ inputs : Fin q → G, ∀ hinputs : Function.Injective inputs,
      let hq : q ≤ Fintype.card G := by
        simpa [Fintype.card_fin] using Fintype.card_le_of_injective inputs hinputs
      (∑ y : Fin q → G,
        max
          (((compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).density
              (transcriptEmbed inputs y)) * (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0) ≤ ε) :
    advantageOn (xopRealPDS (G := G) (q := q)) (xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine nonadaptive_securityOn_injective_from_transcript_bound
    (M := xopSecurityInstance (G := G) (q := q) ε) ?_
  intro inputs hinputs
  have hq : q ≤ Fintype.card G := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective inputs hinputs
  have hC := realizes_xop_compatibleCount_of_visible_positiveError
    (G := G) (q := q) ε inputs hinputs hq (hvisible inputs hinputs)
  rcases hC with ⟨hC⟩
  exact statDist_le_of_densityRatioPositiveError
    ((xopRealPDS (G := G) (q := q)).transcriptDist inputs)
    ((xopIdealPDS (G := G) (q := q)).transcriptDist inputs)
    hC.model.density
    ε
    (densityRatioPositiveError_of_normalizedCounting hC.model)

/-- A pure visible-tuple positive-error estimate implies the restricted
non-adaptive XoP advantage bound. -/
theorem xop_advantageOn_injective_of_pure_visible_positiveError
    [Nonempty G]
    (ε : NNReal)
    (hpure : ∀ _hq : q ≤ Fintype.card G,
      (∑ y : Fin q → G,
        max
          ((compatibleCountNNReal y /
              ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
                  NNReal) /
                (((Fintype.card G ^ q : Nat) : NNReal)))) *
            (Dist.uniform (Fin q → G) y) -
            Dist.uniform (Fin q → G) y) 0) ≤ ε) :
    advantageOn (xopRealPDS (G := G) (q := q)) (xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine xop_advantageOn_injective_of_visible_positiveError (G := G) (q := q) ε ?_
  intro inputs hinputs
  dsimp only
  have hq : q ≤ Fintype.card G := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective inputs hinputs
  rw [visiblePositiveError_xop_compatibleCount_eq_count (G := G) (q := q) inputs hq]
  exact hpure hq

omit [DecidableEq G] in
/--
The embedded-output form of the ideal expectation of the compatible count is
the corrected normalizer `(N)_q^2 / N^q`.
-/
theorem idealEmbeddedExpectation_eq_descFactorial_sq_div_pow (inputs : Fin q → G) :
    (∑ y : Fin q → G,
        (Dist.uniform (Fin q → G) y) * compatibleTranscriptCountNNReal (transcriptEmbed inputs y)) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        Real) / ((Fintype.card G ^ q : Nat) : Real) := by
  have hsum :
      (∑ y : Fin q → G, (compatibleCountNNReal y : Real)) =
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : Real) := by
    exact_mod_cast
      (sum_compatibleCountNNReal_eq_descFactorial_sq (G := G) (q := q))
  calc
    (∑ y : Fin q → G,
        (Dist.uniform (Fin q → G) y) * compatibleTranscriptCountNNReal (transcriptEmbed inputs y))
        = ∑ y : Fin q → G,
            ((1 : Real) / (Fintype.card (Fin q → G) : Real)) *
              (compatibleCountNNReal y : Real) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Dist.uniform_apply, compatibleTranscriptCountNNReal_transcriptEmbed]
    _ = ((1 : Real) / (Fintype.card (Fin q → G) : Real)) *
          ∑ y : Fin q → G, (compatibleCountNNReal y : Real) := by
          rw [Finset.mul_sum]
    _ = ((1 : Real) / ((Fintype.card G ^ q : Nat) : Real)) *
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : Nat) : Real) := by
          rw [hsum, visibleTupleCount_eq_pow]
    _ = (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : Real) /
        ((Fintype.card G ^ q : Nat) : Real) := by ring

/-- Full ideal fixed-input expectation of the compatible transcript count. -/
theorem xopIdeal_compatibleExpectation_eq_descFactorial_sq_div_pow [Nonempty G]
    (inputs : Fin q → G) (h_inj : Function.Injective inputs) :
    (∑ t : Transcript G G q,
        (xopIdealPDS (G := G) (q := q)).transcriptDist inputs t *
          compatibleTranscriptCountNNReal t) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        Real) / ((Fintype.card G ^ q : Nat) : Real) := by
  rw [xopIdeal_transcriptDist_eq_uniform_outputs inputs h_inj]
  rw [Dist.fTransform_sum_mul]
  exact idealEmbeddedExpectation_eq_descFactorial_sq_div_pow inputs

omit [Fintype G] [DecidableEq G] in
/-- The visible output tuple of `xopDDS`. -/
theorem transcriptOutputs_xopDDS (π₁ π₂ : Equiv.Perm G) (inputs : Fin q → G) :
    Combinatorics.transcriptOutputs (DDS.transcript (xopDDS (q := q) π₁ π₂) inputs) =
      fun i => -π₁ (inputs i) + π₂ (inputs i) := by
  funext i
  simp [Combinatorics.transcriptOutputs, xopDDS, DDS.transcript, DDS.ofFunq]

omit [Fintype G] [DecidableEq G] in
/-- Shifting the `π₁` hidden tuple by the XoP visible outputs gives the `π₂` tuple. -/
theorem shifted_transcriptOutputs_xopDDS (π₁ π₂ : Equiv.Perm G) (inputs : Fin q → G) :
    shifted (Combinatorics.transcriptOutputs (DDS.transcript (xopDDS (q := q) π₁ π₂) inputs))
        (hiddenTuple (q := q) π₁ inputs) =
      hiddenTuple (q := q) π₂ inputs := by
  funext i
  simp [shifted, hiddenTuple, transcriptOutputs_xopDDS]

omit [Fintype G] [DecidableEq G] in
/-- For injective fixed inputs, the hidden tuple is compatible with the XoP output tuple. -/
theorem compatibleHiddenState_xopDDS (π₁ π₂ : Equiv.Perm G) (inputs : Fin q → G)
    (hinputs : Function.Injective inputs) :
    CompatibleHiddenState
      (Combinatorics.transcriptOutputs (DDS.transcript (xopDDS (q := q) π₁ π₂) inputs))
      (hiddenTuple (q := q) π₁ inputs) := by
  constructor
  · exact π₁.injective.comp hinputs
  · rw [shifted_transcriptOutputs_xopDDS]
    exact π₂.injective.comp hinputs

end Model
end XoP
end Applications
end RandomSystems
