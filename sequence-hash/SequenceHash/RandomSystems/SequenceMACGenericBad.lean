import SequenceHash.RandomSystems.SequenceMACGenericTrace
import SequenceHash.RandomSystems.SequenceFunctionSeparation

/-!
# SequenceFunction compression-freshness event

This module is the second, definition-only layer of the R4 ideal-compression
development.  It fixes the compression-call freshness event and the key/input
separation hypotheses used by the later equality-on-good and bad-mass layers.
-/

noncomputable section

open scoped NNReal

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems
open RandomSystems.CR18
open RandomSystems.HTechnique.IdealCompression

universe uBlock

/-! ## Ordered compression inputs and the bad event -/

/-- Direct compression inputs visible in the transcript, in visible query
order.  Evaluation queries contribute no entry to this list. -/
def sequenceFunctionVisiblePrimInputs {Block : Type uBlock} {L : U128}
    {users p q : ℕ}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q)) :
    List (HashOutput L × Block) :=
  t.1.toList.filterMap fun query =>
    match query with
    | .prim input => some input
    | .eval _ => none

/-- Revealed construction calls in the fixed convention used by `Bad_SEQ`:
evaluation slots are ordered by `Fin q`, entries within a padded trace by
`Fin lambda`, and padding entries are omitted.  The reveal maps in the next
layer populate these entries from `sequenceFunctionCompressionTrace`. -/
def sequenceFunctionRevealedConstructionCalls {Block : Type uBlock}
    {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    List (TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block) :=
  (List.ofFn fun evalSlot : Fin q =>
      (List.ofFn fun callSlot : Fin lambda =>
        z.evalTraces evalSlot callSlot).filterMap id).flatten

/-- Inputs of all revealed construction compression calls, in the same order
as `sequenceFunctionRevealedConstructionCalls`. -/
def sequenceFunctionRevealedConstructionInputs {Block : Type uBlock}
    {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    List (HashOutput L × Block) :=
  (sequenceFunctionRevealedConstructionCalls z).map TraceEntry.input

/-- Compression-call freshness failure on the ideal extension.

All visible `Prim` inputs are conventionally ordered before all construction
calls.  Consequently the first disjunct says that a construction call repeats
a prior `Prim` call.  The second says that, in evaluation-slot/call-slot order,
some construction call repeats an earlier construction call.  Roles are not
filtered: both same-role and cross-role internal collisions are bad. -/
def Bad_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ} :
    TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda → Prop :=
  fun tz =>
    (∃ input,
      input ∈ sequenceFunctionRevealedConstructionInputs tz.2 ∧
      input ∈ sequenceFunctionVisiblePrimInputs tz.1) ∨
    ¬ (sequenceFunctionRevealedConstructionInputs tz.2).Nodup

/-! ## Conditional sampled-key entropy -/

/-- Conditional per-user point-mass bound for an arbitrary joint user-key
law.  After fixing a complete assignment of every *other* user's key, the
mass of any value for user `i` is at most `2^{-kappaStar}` times the mass of
that conditioning assignment.

This ratio-free form also covers zero-mass conditioning events and is exactly
the conditional min-entropy strength needed for a later `KeyRepeat` union
bound; marginal point-mass bounds alone do not imply it. -/
def KeyPointMassBound {users : ℕ}
    (DK : Dist.ProbDist (Fin users → SequenceMACKey))
    (kappaStar : ℕ) : Prop :=
  ∀ (i : Fin users) (key : SequenceMACKey)
      (otherKeys : {j : Fin users // j ≠ i} → SequenceMACKey),
    DK.val.mass (fun keys =>
        keys i = key ∧
          ∀ j : {j : Fin users // j ≠ i}, keys j.1 = otherKeys j) ≤
      ((2 : NNReal) ^ kappaStar)⁻¹ *
        DK.val.mass (fun keys =>
          ∀ j : {j : Fin users // j ≠ i}, keys j.1 = otherKeys j)

/-! ## Input-level cross-role separation -/

/-- Input-level separation of the four canonical SequenceFunction roles.

The raw derivation roles are present only in their long-input cases.  Their
separation hypotheses are exactly the public R5 residuals:
`DerivePrefixHit_SEQ` for the sampled key and `DeriveSafeS_SEQ` for the fixed
customization.  This predicate says nothing about internal MD compression
inputs; those collisions remain in `Bad_SEQ`. -/
structure SequenceFunctionCrossRoleSeparated
    (b : BlockSize) (S : ByteString) : Prop where
  inner_ne_outer :
    ∀ {L : U128} (K : SequenceMACKey) (M N : InputSequence)
      (derivedKInner derivedSOuter derivedKOuter : List Byte)
      (inner : HashOutput L),
      sequenceFunctionInnerInput b fSeqMac K.1 derivedKInner M ≠
        sequenceFunctionOuterInput b fSeqMac K.1 S N
          derivedKOuter derivedSOuter inner
  keyDerive_ne_framed :
    ∀ {L : U128} (K : SequenceMACKey)
      (M : InputSequence) (derivedK derivedS : List Byte)
      (inner : HashOutput L),
      b.val < K.1.val.length →
        ¬ DerivePrefixHit_SEQ b S K →
          K.1.val ≠ sequenceFunctionInnerInput b fSeqMac K.1 derivedK M ∧
            K.1.val ≠ sequenceFunctionOuterInput b fSeqMac K.1 S M
              derivedK derivedS inner
  customizationDerive_ne_framed :
    ∀ {L : U128} (DK : RandomSystems.Dist SequenceMACKey)
      (K : SequenceMACKey) (M : InputSequence)
      (derivedK derivedS : List Byte) (inner : HashOutput L),
      DeriveSafeS_SEQ b S DK → K ∈ DK.support →
        b.val < S.val.length →
          S.val ≠ sequenceFunctionInnerInput b fSeqMac K.1 derivedK M ∧
            S.val ≠ sequenceFunctionOuterInput b fSeqMac K.1 S M
              derivedK derivedS inner
  keyDerive_ne_customizationDerive :
    ∀ K : SequenceMACKey,
      b.val < K.1.val.length → b.val < S.val.length →
        ¬ DerivePrefixHit_SEQ b S K → K.1.val ≠ S.val

/-- The canonical SequenceFunction inputs satisfy the input-level cross-role
predicate under precisely its stated raw-derivation residual hypotheses.  The
proof reuses the public DomainSeparation and R5 bridge theorems. -/
theorem sequenceFunctionCrossRoleSeparated (b : BlockSize) (S : ByteString) :
    SequenceFunctionCrossRoleSeparated b S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sequenceFunctionInnerInput_ne_outerInput b S
  · intro L K M derivedK derivedS inner hLongK hSafeK
    have hPrefixes :
        ¬ List.IsPrefix (headerI b fSeqMac K.1) K.1.val ∧
        ¬ List.IsPrefix (headerO b fSeqMac S K.1) K.1.val := by
      constructor <;> intro hPrefix <;> apply hSafeK <;>
        exact ⟨hLongK, by aesop⟩
    exact
      ⟨sequenceFunctionDeriveInput_ne_innerInput_of_not_prefix
          b K K.1.val derivedK M hPrefixes.1,
        sequenceFunctionDeriveInput_ne_outerInput_of_not_prefix
          b S K K.1.val M derivedK derivedS inner hPrefixes.2⟩
  · intro L DK K M derivedK derivedS inner hSafeS hK hLongS
    have hPrefixes :
        ¬ List.IsPrefix (headerI b fSeqMac K.1) S.val ∧
        ¬ List.IsPrefix (headerO b fSeqMac S K.1) S.val := by
      rcases hSafeS with hShortS | hSafeS
      · omega
      · exact hSafeS K hK
    exact
      ⟨sequenceFunctionDeriveInput_ne_innerInput_of_not_prefix
          b K S.val derivedK M hPrefixes.1,
        sequenceFunctionDeriveInput_ne_outerInput_of_not_prefix
          b S K S.val M derivedK derivedS inner hPrefixes.2⟩
  · intro K hLongK hLongS hSafeK hEq
    apply hSafeK
    exact ⟨hLongK, Or.inl ⟨hLongS, Subtype.ext hEq⟩⟩

end RandomSystemsModel
end SequenceHash
