import SequenceHash.DomainSeparation
import SequenceHash.RandomSystems.SequenceFunctionCore
import SequenceHash.RandomSystems.SequenceFunctionSeparation

/-!
# Structural DRST discharge for SequenceMAC over Merkle--Damgard

This module performs only the structural R5-to-R3 composition.  The deep
DRST simulator theorem is deliberately an explicit hypothesis: proving its
colored compression-graph router and preimage extractor belongs to the
separate deep development.

The positive DRST object is the complete HMAC-shaped construction, not plain
Merkle--Damgard.  Accordingly, all new construction and cost definitions
below start from canonical `SequenceFunction`; `mdHashDist` merely supplies
its fixed-output hash law.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18

namespace SequenceHash

open RandomSystems RandomSystems.CR18

namespace RandomSystemsModel

/-- Existing SequenceMAC is exactly canonical `SequenceFunction` at `F = 1`. -/
theorem sequenceMAC_eq_sequenceFunction {L : U128} (b : BlockSize)
    (H : FixedHash L) (S : ByteString) (K : SequenceMACKey)
    (M : InputSequence) :
    sequenceMAC b H S K M = sequenceFunction b H K.1 S fSeqMac M := by
  rfl

/-- Existing SequenceMAC's converter step is exactly the canonical
`SequenceFunction` schedule at `F = 1`. -/
theorem sequenceMACStep_eq_sequenceFunctionStep {L : U128} (b : BlockSize)
    (S : ByteString) (K : SequenceMACKey) (M : InputSequence)
    (ys : List (HashOutput L)) :
    sequenceMACStep b S K M ys =
      sequenceFunctionStep b K.1 S fSeqMac M ys := by
  rfl

/-! ## MD law, DRST error, and compression-cost accounting -/

/-- The fixed-output MD hash law obtained by pushing a compression-function
law through `mdHash codec · iv`. -/
noncomputable def mdHashDist {Block : Type*} {L : U128}
    (codec : MDCodec Block)
    (Df : RandomSystems.Dist (Compression (HashOutput L) Block))
    (iv : HashOutput L) : RandomSystems.Dist (FixedHash L) :=
  RandomSystems.Dist.fTransform (fun f => mdHash codec f iv) Df

/-- DRST Theorem 4.4's `13 * Sigma^2 / 2^n` envelope.  A C2SP digest has
`n = 8 * L` bits. -/
noncomputable def drstError {L : U128} (totalCost : ℕ) : NNReal :=
  13 * (totalCost : NNReal) ^ 2 / (2 : NNReal) ^ (8 * L.val)

/-! ## The exact raw-Derive residual -/

/-- The exact probability mass of the sampled-key raw-Derive prefix-hit
event.  The key is sampled once and reused, so this term is not multiplied
by the outside query count. -/
noncomputable def DeriveCost_SEQ (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey) : NNReal :=
  DK.mass (DerivePrefixHit_SEQ b S)

/-- Outside `DerivePrefixHit_SEQ`, a long raw key input is separated from
both framed roles by the existing DomainSeparation lemmas. -/
theorem sequenceMAC_keyDerive_separated_of_not_prefixHit {L : U128}
    (b : BlockSize) (S : ByteString) (K : SequenceMACKey)
    (hLongK : b.val < K.1.val.length)
    (hSafeK : ¬ DerivePrefixHit_SEQ b S K)
    (M : InputSequence) (derivedK derivedS : List Byte)
    (inner : HashOutput L) :
    K.1.val ≠ sequenceMACInnerInput b K derivedK M ∧
      K.1.val ≠ sequenceMACOuterInput b S K M derivedS derivedK inner := by
  have hPrefixes :
      ¬ List.IsPrefix (headerI b fSeqMac K.1) K.1.val ∧
      ¬ List.IsPrefix (headerO b fSeqMac S K.1) K.1.val := by
    constructor <;> intro hPrefix <;> apply hSafeK <;>
      exact ⟨hLongK, by aesop⟩
  exact
    ⟨sequenceMACDeriveInput_ne_innerInput_of_not_prefix
        b K K.1.val derivedK M hPrefixes.1,
      sequenceMACDeriveInput_ne_outerInput_of_not_prefix
        b S K K.1.val M derivedS derivedK inner hPrefixes.2⟩

/-- Under `DeriveSafeS_SEQ`, every supported long raw customization input is
separated from both framed roles by the existing DomainSeparation lemmas. -/
theorem sequenceMAC_customizationDerive_separated_of_safe
    {L : U128} (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey) (hSafeS : DeriveSafeS_SEQ b S DK)
    (K : SequenceMACKey) (hK : K ∈ DK.support)
    (hLongS : b.val < S.val.length) (M : InputSequence)
    (derivedK derivedS : List Byte) (inner : HashOutput L) :
    S.val ≠ sequenceMACInnerInput b K derivedK M ∧
      S.val ≠ sequenceMACOuterInput b S K M derivedS derivedK inner := by
  have hPrefixes :
      ¬ List.IsPrefix (headerI b fSeqMac K.1) S.val ∧
      ¬ List.IsPrefix (headerO b fSeqMac S K.1) S.val := by
    rcases hSafeS with hShortS | hSafeS
    · omega
    · exact hSafeS K hK
  exact
    ⟨sequenceMACDeriveInput_ne_innerInput_of_not_prefix
        b K S.val derivedK M hPrefixes.1,
      sequenceMACDeriveInput_ne_outerInput_of_not_prefix
        b S K S.val M derivedS derivedK inner hPrefixes.2⟩

/-! ## Structural DRST hypothesis and the frozen R3 discharge -/

/-- The structural R5 corollary in R3's frozen `h_indiff` shape.  The DRST
simulator bound is an explicit named hypothesis; this theorem only transports
its NNReal error into the chosen `epsilon_ind` envelope. -/
theorem sequenceMAC_md_h_indiff {Block : Type*} {L : U128}
    (q : ℕ) (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (codec : MDCodec Block)
    (Df : RandomSystems.Dist (Compression (HashOutput L) Block))
    (iv : HashOutput L) (ε_ind : ℕ → NNReal)
    (h_drst :
      Δ(⌈q⌉ SM_H b S DK (mdHashDist codec Df iv),
          ⌈q⌉ SM_RO_separated b S DK) ≤
        (drstError (L := L)
            (sequenceFunctionCompressionCost codec b S L (4 * q) 0) +
          (if q = 0 then 0 else DeriveCost_SEQ b S DK) : ℝ))
    (hepsilon :
      drstError (L := L)
          (sequenceFunctionCompressionCost codec b S L (4 * q) 0) +
        (if q = 0 then 0 else DeriveCost_SEQ b S DK) ≤ ε_ind (4 * q)) :
    Δ(⌈q⌉ SM_H b S DK (mdHashDist codec Df iv),
        ⌈q⌉ SM_RO_separated b S DK) ≤ (ε_ind (4 * q) : ℝ) := by
  apply le_trans h_drst
  exact_mod_cast hepsilon

/-- End-to-end R1--R5 SequenceMAC PRF bound, conditional only on the named
DRST simulator bound, its selected error envelope, and normalization of the
sampled-key law. -/
theorem sequenceMAC_md_prf_bound_indiff {Block : Type*} {L : U128}
    (q : ℕ) (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (codec : MDCodec Block)
    (Df : RandomSystems.Dist (Compression (HashOutput L) Block))
    (iv : HashOutput L) (ε_ind : ℕ → NNReal)
    (hDK : DK.isProbDist)
    (h_drst :
      Δ(⌈q⌉ SM_H b S DK (mdHashDist codec Df iv),
          ⌈q⌉ SM_RO_separated b S DK) ≤
        (drstError (L := L)
            (sequenceFunctionCompressionCost codec b S L (4 * q) 0) +
          (if q = 0 then 0 else DeriveCost_SEQ b S DK) : ℝ))
    (hepsilon :
      drstError (L := L)
          (sequenceFunctionCompressionCost codec b S L (4 * q) 0) +
        (if q = 0 then 0 else DeriveCost_SEQ b S DK) ≤ ε_ind (4 * q)) :
    Δ(⌈q⌉ SM_H b S DK (mdHashDist codec Df iv),
        ⌈q⌉ PFunPDS.URF (X := InputSequence) (Y := HashOutput L)) ≤
      (ε_ind (4 * q) : ℝ) +
        (pairCollisionUnionBound (HashOutput L) q : ℝ) := by
  apply sequenceMAC_prf_bound_indiff q b S DK (mdHashDist codec Df iv)
    ε_ind hDK
  exact sequenceMAC_md_h_indiff q b S DK codec Df iv ε_ind h_drst hepsilon

end RandomSystemsModel

end SequenceHash
