/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.Derivation

/-!
# Rectangular adaptive Hash-then-PRF

The reusable Hash-then-PRF construction already permits different message and
response types, but the tight adaptive stress test in
`RandomSystems.HTechnique.Derivation` specializes both to one type.  This file
instantiates the same representative-level H-technique argument without that
specialization.

The proof reveals the hash key in both worlds.  Away from collisions of
distinct transcript inputs, the real and ideal extended fixed-query masses are
equal.  In the ideal world the revealed key is independent of the transcript,
so epsilon-universality and the pair union bound give the adaptive bad-event
bound directly.
-/

noncomputable section

open scoped BigOperators NNReal RandomSystems.CR18

namespace SequenceHash.RectHashThenPRF

open RandomSystems
open RandomSystems.CR18
open RandomSystems.HTechnique.HashThenPRF
open RandomSystems.CR18.HTechniqueDerivation
open PFunPDE (transcriptSystemFactor transcriptSystemEvent)
open PFunPDS.Prob (urf)

attribute [local instance] Classical.propDecidable

variable {K M H Y : Type*} {q : Nat}
variable [Fintype K] [Nonempty K] [Fintype M] [Fintype H]
variable [Fintype Y] [Nonempty Y]
variable [FiniteTranscriptSpace M Y q]

/-- Real representative: a uniform hash key and an independent uniform
function from hash values to responses. -/
noncomputable abbrev realP : Dist.ProbDist (K × (H → Y)) :=
  Dist.prodProbDist
    (⟨Dist.uniform K, Dist.uniform_isProbDist⟩ : Dist.ProbDist K)
    (⟨Dist.uniform (H → Y), Dist.uniform_isProbDist⟩ :
      Dist.ProbDist (H → Y))

/-- The sampled real Hash-then-PRF system. -/
noncomputable abbrev realF (Hf : EpsUniversalHash K M H) :
    PFunPDS.RV (K × (H → Y)) M Y :=
  functionEvaluatorRV (fun p => hashThenPRF Hf p.1 p.2)

/-- Ideal representative: an independent dummy hash key and a uniform random
function from messages to responses. -/
noncomputable abbrev idealP : Dist.ProbDist (K × (M → Y)) :=
  Dist.prodProbDist
    (⟨Dist.uniform K, Dist.uniform_isProbDist⟩ : Dist.ProbDist K)
    (⟨Dist.uniform (M → Y), Dist.uniform_isProbDist⟩ :
      Dist.ProbDist (M → Y))

/-- The sampled ideal system ignores the dummy key. -/
noncomputable abbrev idealF : PFunPDS.RV (K × (M → Y)) M Y :=
  functionEvaluatorRV (fun p => p.2)

/-- Reveal the real or dummy hash key. -/
abbrev keyAug {Omega : Type*} :
    (K × Omega) → TranscriptPrefix M Y q → K :=
  fun p _ => p.1

/-- Bad extended transcripts contain two distinct message inputs that collide
under the revealed hash key. -/
def HashBad (Hf : EpsUniversalHash K M H)
    (tz : TranscriptPrefix M Y q × K) : Prop :=
  ∃ i j : Fin q, tz.1.1.get i ≠ tz.1.1.get j ∧
    Hf.hash tz.2 (tz.1.1.get i) = Hf.hash tz.2 (tz.1.1.get j)

omit [Fintype M] [FiniteTranscriptSpace M Y q] in
/-- Closed form for the real representative's extended system factor. -/
theorem extSysFactorRep_real_apply (Hf : EpsUniversalHash K M H)
    (xv : List.Vector M q) (yv : List.Vector Y q) (h : K) :
    extSysFactorRep (realP (K := K) (H := H) (Y := Y)) (realF Hf) keyAug
        ((xv, yv), h) =
      Dist.uniform K h *
        (Dist.uniform (H → Y)).mass
          (fun rho => ∀ i : Fin q,
            rho (Hf.hash h (xv.get i)) = yv.get i) := by
  unfold extSysFactorRep
  rw [show (fun omega : K × (H → Y) =>
      transcriptSystemEvent (realF Hf) ((xv, yv), h).1.1
          ((xv, yv), h).1.2 omega ∧
        keyAug omega ((xv, yv), h).1 = ((xv, yv), h).2) =
    (fun omega : K × (H → Y) =>
      (∀ i : Fin q,
          omega.2 (Hf.hash omega.1 (xv.get i)) = yv.get i) ∧
        omega.1 = h) from
    funext fun omega => propext (Iff.intro
      (fun hev =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv omega).mp
            hev.1,
          hev.2⟩)
      (fun hev =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv omega).mpr
            hev.1,
          hev.2⟩))]
  exact mass_prod_fst_eq _ _ h
    (fun (h' : K) (rho : H → Y) =>
      ∀ i : Fin q, rho (Hf.hash h' (xv.get i)) = yv.get i)

omit [FiniteTranscriptSpace M Y q] in
/-- Closed form for the ideal representative's extended system factor. -/
theorem extSysFactorRep_ideal_apply
    (xv : List.Vector M q) (yv : List.Vector Y q) (h : K) :
    extSysFactorRep (idealP (K := K) (M := M) (Y := Y))
        (idealF (K := K)) keyAug ((xv, yv), h) =
      Dist.uniform K h *
        (Dist.uniform (M → Y)).mass
          (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) := by
  unfold extSysFactorRep
  rw [show (fun omega : K × (M → Y) =>
      transcriptSystemEvent (idealF (K := K)) ((xv, yv), h).1.1
          ((xv, yv), h).1.2 omega ∧
        keyAug omega ((xv, yv), h).1 = ((xv, yv), h).2) =
    (fun omega : K × (M → Y) =>
      (∀ i : Fin q, omega.2 (xv.get i) = yv.get i) ∧ omega.1 = h) from
    funext fun omega => propext (Iff.intro
      (fun hev =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv omega).mp
            hev.1,
          hev.2⟩)
      (fun hev =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv omega).mpr
            hev.1,
          hev.2⟩))]
  exact mass_prod_fst_eq _ _ h
    (fun (_ : K) (g : M → Y) =>
      ∀ i : Fin q, g (xv.get i) = yv.get i)

omit [FiniteTranscriptSpace M Y q] in
/-- The dummy key sums out of the ideal system factor. -/
theorem sysFactor_ideal_eq
    (xv : List.Vector M q) (yv : List.Vector Y q) :
    transcriptSystemFactor (idealP (K := K) (M := M) (Y := Y))
        (idealF (K := K)) xv yv =
      (Dist.uniform (M → Y)).mass
        (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) := by
  unfold transcriptSystemFactor
  rw [show transcriptSystemEvent (idealF (K := K)) xv yv =
      (fun omega : K × (M → Y) =>
        ∀ i : Fin q, omega.2 (xv.get i) = yv.get i) from
    funext fun omega => propext
      (transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv omega)]
  exact (mass_prod_snd_pred (Dist.uniform K) (Dist.uniform (M → Y))
      (fun g : M → Y => ∀ i : Fin q, g (xv.get i) = yv.get i)).trans
    (by rw [show (Dist.uniform K).weight = 1 from Dist.uniform_isProbDist,
      one_mul])

/-- On good extended transcripts, the real and ideal fixed-query masses are
identical.  The proof uses only equality-pattern preservation; it therefore
handles repeated adaptive queries without assuming an injective query vector. -/
theorem extFixedQuery_eq_on_good (Hf : EpsUniversalHash K M H)
    (xs : Fin q → M) (tz : TranscriptPrefix M Y q × K)
    (h_good : ¬ HashBad Hf tz) :
    extFixedQueryTranscriptDistRep
        (realP (K := K) (H := H) (Y := Y)) (realF Hf) keyAug xs tz =
      extFixedQueryTranscriptDistRep
        (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K)) keyAug xs tz := by
  classical
  obtain ⟨⟨xv, yv⟩, h⟩ := tz
  unfold extFixedQueryTranscriptDistRep
  rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply]
  congr 1
  rw [extSysFactorRep_real_apply, extSysFactorRep_ideal_apply]
  congr 1
  have hpattern : ∀ i j : Fin q,
      Hf.hash h (xv.get i) = Hf.hash h (xv.get j) ↔
        xv.get i = xv.get j := by
    intro i j
    constructor
    · intro hhash
      by_contra hne
      exact h_good ⟨i, j, hne, hhash⟩
    · intro hx
      rw [hx]
  have hcondition :
      (∀ i j : Fin q,
          Hf.hash h (xv.get i) = Hf.hash h (xv.get j) →
            yv.get i = yv.get j) ↔
        (∀ i j : Fin q, xv.get i = xv.get j → yv.get i = yv.get j) := by
    constructor <;> intro hc i j hij
    · exact hc i j (by rw [hij])
    · exact hc i j ((hpattern i j).mp hij)
  have hcard : Fintype.card
      {x : H // x ∈ queryImageSet (fun i => Hf.hash h (xv.get i))} =
      Fintype.card {x : M // x ∈ queryImageSet (fun i => xv.get i)} := by
    rw [Fintype.card_coe, Fintype.card_coe]
    unfold queryImageSet
    rw [show ((Finset.univ : Finset (Fin q)).image
        fun i => Hf.hash h (xv.get i)) =
        ((Finset.univ : Finset (Fin q)).image fun i => xv.get i).image
          (Hf.hash h) from by rw [Finset.image_image]; rfl]
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact (hpattern i j).mp hab
  calc
    (Dist.uniform (H → Y)).mass
        (fun rho => ∀ i : Fin q,
          rho (Hf.hash h (xv.get i)) = yv.get i)
        = (Dist.fTransform
            (fun f : H → Y => fun i => f (Hf.hash h (xv.get i)))
            (Dist.uniform (H → Y)))
          (fun i => yv.get i) := mass_eval_eq_apply _ _ _
    _ = (if ∀ i j : Fin q,
          Hf.hash h (xv.get i) = Hf.hash h (xv.get j) →
            yv.get i = yv.get j then
          ((Fintype.card Y : NNReal) ^ Fintype.card
            {x : H // x ∈ queryImageSet
              (fun i => Hf.hash h (xv.get i))})⁻¹
        else 0) := uniformFunction_eval_apply _ _
    _ = (if ∀ i j : Fin q,
          xv.get i = xv.get j → yv.get i = yv.get j then
          ((Fintype.card Y : NNReal) ^ Fintype.card
            {x : M // x ∈ queryImageSet (fun i => xv.get i)})⁻¹
        else 0) := by
          simp only [hcondition]
          rw [hcard]
    _ = (Dist.fTransform (fun f : M → Y => fun i => f (xv.get i))
          (Dist.uniform (M → Y))) (fun i => yv.get i) :=
        (uniformFunction_eval_apply _ _).symm
    _ = (Dist.uniform (M → Y)).mass
          (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) :=
        (mass_eval_eq_apply _ _ _).symm

omit [Fintype H] in
/-- Per-transcript bad-key bound, reduced to the injective compressed query
tuple supplied by the generic HashThenPRF library. -/
theorem uniformK_hashBadAt_le (Hf : EpsUniversalHash K M H)
    (xv : List.Vector M q) :
    (Dist.uniform K).mass (fun h => ∃ i j : Fin q,
        xv.get i ≠ xv.get j ∧
        Hf.hash h (xv.get i) = Hf.hash h (xv.get j)) ≤
      choose2 q * Hf.eps := by
  classical
  set u : Fin q → M := fun i => xv.get i with hu
  have hbridge : ∀ h : K,
      (∃ i j : Fin q, xv.get i ≠ xv.get j ∧
          Hf.hash h (xv.get i) = Hf.hash h (xv.get j)) ↔
        hashCollision Hf h (compressedQuery u) := by
    intro h
    constructor
    · rintro ⟨i, j, hne, hcol⟩
      refine ⟨compressedQueryIndex u i, compressedQueryIndex u j, ?_, ?_⟩
      · intro hab
        have heq := congrArg (compressedQuery u) hab
        rw [compressedQuery_compressedQueryIndex,
          compressedQuery_compressedQueryIndex] at heq
        exact hne heq
      · have heq : Hf.hash h (u i) = Hf.hash h (u j) := hcol
        rw [← compressedQuery_compressedQueryIndex u i,
          ← compressedQuery_compressedQueryIndex u j] at heq
        exact heq
    · rintro ⟨a, b, hab, hcol⟩
      obtain ⟨i, rfl⟩ := compressedQueryIndex_surjective u a
      obtain ⟨j, rfl⟩ := compressedQueryIndex_surjective u b
      refine ⟨i, j, ?_, ?_⟩
      · intro hx
        refine hab ?_
        unfold compressedQueryIndex
        exact congrArg _ (Subtype.ext (show u i = u j from hx))
      · have heq :
            Hf.hash h (compressedQuery u (compressedQueryIndex u i)) =
              Hf.hash h (compressedQuery u (compressedQueryIndex u j)) :=
          hcol
        rw [compressedQuery_compressedQueryIndex,
          compressedQuery_compressedQueryIndex] at heq
        exact heq
  rw [Dist.mass_congr _ hbridge]
  refine le_trans
    (hashCollision_prob_le Hf (compressedQuery u)
      (compressedQuery_injective u)) ?_
  gcongr
  exact_mod_cast Nat.choose_le_choose 2 (compressedQuery_card_le u)

omit [Fintype H] in
/-- The ideal system is independent of the dummy key, so the adaptive bad
mass is the transcript average of the per-transcript epsilon-universality
bound. -/
theorem ideal_probBad_le (Hf : EpsUniversalHash K M H)
    (E : QQueryEnvironment M Y q) :
    Pr[HashBad Hf ∣
        extendedTranscriptDistRep (q := q)
          (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
          keyAug E.1] ≤
      choose2 q * Hf.eps := by
  classical
  have hIdealTotal : PFunPDS.Prob.KStepTotal
      (Dist.PMF (idealP (K := K) (M := M) (Y := Y))
        (idealF (K := K))) q :=
    functionEvaluatorProb_KStepTotal
      (idealP (K := K) (M := M) (Y := Y)) (fun p => p.2) q
  have hmass :
      Pr[HashBad Hf ∣
          extendedTranscriptDistRep (q := q)
            (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
            keyAug E.1] =
        ∑ t : TranscriptPrefix M Y q, ∑ h : K,
          if HashBad Hf (t, h) then
            extendedTranscriptDistRep (q := q)
              (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
              keyAug E.1 (t, h)
          else 0 := by
    rw [show Pr[HashBad Hf ∣
        extendedTranscriptDistRep (q := q)
          (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
          keyAug E.1] =
      (extendedTranscriptDistRep (q := q)
        (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
        keyAug E.1).mass (HashBad Hf) from rfl]
    rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  rw [hmass]
  have hinner : ∀ t : TranscriptPrefix M Y q,
      (∑ h : K,
        if HashBad Hf (t, h) then
          extendedTranscriptDistRep (q := q)
            (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
            keyAug E.1 (t, h)
        else 0) ≤
      (choose2 q * Hf.eps) *
        tr[q]((Dist.PMF (idealP (K := K) (M := M) (Y := Y))
          (idealF (K := K)) : ProbPDS M Y), E.1) t := by
    intro t
    obtain ⟨xv, yv⟩ := t
    calc
      (∑ h : K,
          if HashBad Hf ((xv, yv), h) then
            extendedTranscriptDistRep (q := q)
              (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
              keyAug E.1 ((xv, yv), h)
          else 0)
          = (∑ h : K,
              if HashBad Hf ((xv, yv), h) then Dist.uniform K h else 0) *
            ((Dist.uniform (M → Y)).mass
              (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) *
              η(E.1) (xv, yv)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [extendedTranscriptDistRep_apply,
              extSysFactorRep_ideal_apply]
            by_cases hb : HashBad Hf ((xv, yv), h)
            · rw [if_pos hb, if_pos hb]
              ring
            · rw [if_neg hb, if_neg hb, zero_mul]
      _ ≤ (choose2 q * Hf.eps) *
            ((Dist.uniform (M → Y)).mass
              (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) *
              η(E.1) (xv, yv)) := by
            gcongr
            calc
              (∑ h : K,
                  if HashBad Hf ((xv, yv), h) then Dist.uniform K h else 0)
                  = (Dist.uniform K).mass
                      (fun h => HashBad Hf ((xv, yv), h)) :=
                    (Dist.mass_eq_sum _ _).symm
              _ ≤ choose2 q * Hf.eps := by
                    refine le_trans
                      (le_of_eq (Dist.mass_congr _ fun h =>
                        Iff.intro (fun hb => hb) (fun hb => hb))) ?_
                    exact uniformK_hashBadAt_le Hf xv
      _ = (choose2 q * Hf.eps) *
          tr[q]((Dist.PMF (idealP (K := K) (M := M) (Y := Y))
            (idealF (K := K)) : ProbPDS M Y), E.1) (xv, yv) := by
            rw [deterministicTranscriptDist_pmf_apply, sysFactor_ideal_eq]
  calc
    (∑ t : TranscriptPrefix M Y q, ∑ h : K,
        if HashBad Hf (t, h) then
          extendedTranscriptDistRep (q := q)
            (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
            keyAug E.1 (t, h)
        else 0)
        ≤ ∑ t : TranscriptPrefix M Y q,
          (choose2 q * Hf.eps) *
            tr[q]((Dist.PMF (idealP (K := K) (M := M) (Y := Y))
              (idealF (K := K)) : ProbPDS M Y), E.1) t :=
      Finset.sum_le_sum fun t _ => hinner t
    _ = (choose2 q * Hf.eps) *
        (tr[q]((Dist.PMF (idealP (K := K) (M := M) (Y := Y))
          (idealF (K := K)) : ProbPDS M Y), E.1)).weight := by
      rw [← Finset.mul_sum, Dist.weight_eq_sum]
    _ ≤ choose2 q * Hf.eps := by
      rw [deterministicTranscriptDist_weight_eq_one _ E hIdealTotal, mul_one]

/-- The ideal dummy-key representative presents the rectangular URF law. -/
theorem pmf_ideal_eq_urf :
    (Dist.PMF (idealP (K := K) (M := M) (Y := Y))
        (idealF (K := K)) : ProbPDS M Y) =
      urf (X := M) (Y := Y) := by
  refine Subtype.ext ?_
  show Dist.fTransform (idealF (K := K))
      (idealP (K := K) (M := M) (Y := Y)).val =
    Dist.fTransform PFunPDS.urfRV
      (PFunPDS.uniformP (X := M) (Y := Y)).val
  rw [show idealF (K := K) = PFunPDS.urfRV ∘ Prod.snd from rfl,
    ← Dist.fTransform_comp]
  congr 1
  refine Finsupp.ext fun g => ?_
  rw [Dist.fTransform_apply_eq_mass]
  refine ((mass_prod_snd_pred (Dist.uniform K) (Dist.uniform (M → Y))
      (fun g' : M → Y => g' = g)).trans ?_)
  rw [show (Dist.uniform K).weight = 1 from Dist.uniform_isProbDist, one_mul,
    PFunPDS.uniformP_val, Dist.mass_eq_sum]
  refine (Finset.sum_eq_single g (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ g) h)).trans (if_pos rfl)

/-- Tight adaptive security of rectangular Hash-then-PRF:

`Adv[q](HashThenPRF, URF[M,Y]) <= C(q,2) * eps`.

Unlike the square stress-test theorem in `Derivation.lean`, the message type
`M` and response type `Y` are independent. -/
theorem hashThenPRF_adaptive_tight_rect
    (Hf : EpsUniversalHash K M H) :
    Adv[q](hashThenPRFProbPDS (Y := Y) Hf, urf (X := M) (Y := Y)) ≤
      ((choose2 q * Hf.eps : NNReal) : Real) := by
  have hRealTotal : PFunPDS.Prob.KStepTotal
      (Dist.PMF (realP (K := K) (H := H) (Y := Y)) (realF Hf)) q :=
    functionEvaluatorProb_KStepTotal
      (realP (K := K) (H := H) (Y := Y))
      (fun p => hashThenPRF Hf p.1 p.2) q
  have hIdealTotal : PFunPDS.Prob.KStepTotal
      (Dist.PMF (idealP (K := K) (M := M) (Y := Y))
        (idealF (K := K))) q :=
    functionEvaluatorProb_KStepTotal
      (idealP (K := K) (M := M) (Y := Y)) (fun p => p.2) q
  rw [← pmf_ideal_eq_urf (K := K)]
  exact adv_le_of_extFixedQueryRep_eq_on_good
    (realP (K := K) (H := H) (Y := Y)) (realF Hf)
    (idealP (K := K) (M := M) (Y := Y)) (idealF (K := K))
    keyAug keyAug (HashBad Hf) (choose2 q * Hf.eps)
    hRealTotal hIdealTotal (extFixedQuery_eq_on_good Hf)
    (ideal_probBad_le Hf)

end SequenceHash.RectHashThenPRF
