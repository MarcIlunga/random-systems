import RandomSystems.Dist
import SequenceHash.RandomSystems.SequenceFunctionCore

/-!
# SequenceFunction input separation

This module records the byte-level facts needed by the ideal-compression bad
event.  They depend only on the literal construction and the sampled-key law,
not on the PRF or indifferentiability reductions.
-/

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems

/-- The exact raw-key residual: a long key either aliases the long
customization input or begins with one of the two framed role headers. -/
def DerivePrefixHit_SEQ (b : BlockSize) (S : ByteString)
    (K : SequenceMACKey) : Prop :=
  b.val < K.1.val.length ∧
    ((b.val < S.val.length ∧ K.1 = S) ∨
      List.IsPrefix (headerI b fSeqMac K.1) K.1.val ∨
      List.IsPrefix (headerO b fSeqMac S K.1) K.1.val)

/-- The fixed customization is either short, or is prefix-separated from
both framed roles for every supported key. -/
def DeriveSafeS_SEQ (b : BlockSize) (S : ByteString)
    (DK : Dist SequenceMACKey) : Prop :=
  S.val.length ≤ b.val ∨
    ∀ K ∈ DK.support,
      ¬ List.IsPrefix (headerI b fSeqMac K.1) S.val ∧
      ¬ List.IsPrefix (headerO b fSeqMac S K.1) S.val

@[simp]
theorem take_eight_sequenceFunctionInnerInput
    (b : BlockSize) (K : SequenceMACKey) (derivedK : List Byte)
    (M : InputSequence) :
    (sequenceFunctionInnerInput b fSeqMac K.1 derivedK M).take 8 =
      headerIIndicator := by
  unfold sequenceFunctionInnerInput headerI pad
  split
  · simp_all [headerIIndicator]
  · split <;> simp [headerIIndicator]

@[simp]
theorem take_eight_sequenceFunctionOuterInput {L : U128}
    (b : BlockSize) (S : ByteString) (K : SequenceMACKey)
    (M : InputSequence) (derivedK derivedS : List Byte)
    (inner : HashOutput L) :
    (sequenceFunctionOuterInput b fSeqMac K.1 S M derivedK derivedS inner).take 8 =
      headerOIndicator := by
  unfold sequenceFunctionOuterInput headerO pad
  split
  · simp_all [headerOIndicator]
  · split <;> simp [headerOIndicator]

/-- Inner and outer SequenceFunction calls have distinct role indicators. -/
theorem sequenceFunctionInnerInput_ne_outerInput {L : U128}
    (b : BlockSize) (S : ByteString) (K : SequenceMACKey)
    (M N : InputSequence)
    (derivedKInner derivedSOuter derivedKOuter : List Byte)
    (inner : HashOutput L) :
    sequenceFunctionInnerInput b fSeqMac K.1 derivedKInner M ≠
      sequenceFunctionOuterInput b fSeqMac K.1 S N
        derivedKOuter derivedSOuter inner := by
  intro h
  have hIndicators := congrArg (List.take 8) h
  simp only [take_eight_sequenceFunctionInnerInput,
    take_eight_sequenceFunctionOuterInput] at hIndicators
  exact (by decide : headerIIndicator ≠ headerOIndicator) hIndicators

/-- A raw derivation input cannot equal an inner call when it does not begin
with the inner-role header. -/
theorem sequenceFunctionDeriveInput_ne_innerInput_of_not_prefix
    (b : BlockSize) (K : SequenceMACKey)
    (deriveInput derivedK : List Byte) (M : InputSequence)
    (hPrefix : ¬ List.IsPrefix (headerI b fSeqMac K.1) deriveInput) :
    deriveInput ≠ sequenceFunctionInnerInput b fSeqMac K.1 derivedK M := by
  intro h
  apply hPrefix
  rw [h]
  simp [sequenceFunctionInnerInput]

/-- A raw derivation input cannot equal an outer call when it does not begin
with the outer-role header. -/
theorem sequenceFunctionDeriveInput_ne_outerInput_of_not_prefix
    {L : U128} (b : BlockSize) (S : ByteString) (K : SequenceMACKey)
    (deriveInput : List Byte) (M : InputSequence)
    (derivedK derivedS : List Byte) (inner : HashOutput L)
    (hPrefix : ¬ List.IsPrefix (headerO b fSeqMac S K.1) deriveInput) :
    deriveInput ≠ sequenceFunctionOuterInput b fSeqMac K.1 S M
      derivedK derivedS inner := by
  intro h
  apply hPrefix
  rw [h]
  simp [sequenceFunctionOuterInput]

end RandomSystemsModel
end SequenceHash
