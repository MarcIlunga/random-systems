import SequenceHash.RandomSystems.MDHash
import SequenceHash.RandomSystems.Finite

/-!
# Canonical SequenceFunction core

This module contains the construction-level definitions shared by the
SequenceMAC PRF, indifferentiability, and ideal-compression developments.  It
has no dependency on any security reduction: importing the literal
construction must not pull in an unrelated proof chain.
-/

noncomputable section

open scoped BigOperators

namespace SequenceHash

/-! ## Canonical C2SP `SequenceFunction` -/

/-- The canonical inner input of C2SP `SequenceFunction(H,K,S,F;M)` after
the key derivation has been computed. -/
def sequenceFunctionInnerInput (b : BlockSize) (F : U128) (K : ByteString)
    (derivedK : List Byte) (M : InputSequence) : List Byte :=
  headerI b F K ++ derivedK ++ encodeItems M

/-- The canonical outer input of C2SP `SequenceFunction(H,K,S,F;M)` after
the customization and key derivations and the inner hash have been computed. -/
def sequenceFunctionOuterInput {L : U128} (b : BlockSize) (F : U128)
    (K S : ByteString) (M : InputSequence) (derivedK derivedS : List Byte)
    (inner : HashOutput L) : List Byte :=
  headerO b F S K ++ derivedS ++ derivedK ++
    encodeMSBF ⟨M.val.length, M.property⟩ ++ encodeMSBF L ++ inner.val

/-- Canonical C2SP `SequenceFunction(H,K,S,F;M)`. Both derivation results
are computed once and reused by the inner and outer calls. -/
def sequenceFunction {L : U128} (b : BlockSize) (H : FixedHash L)
    (K S : ByteString) (F : U128) (M : InputSequence) : HashOutput L :=
  let derivedK := derive K.val H b
  let derivedS := derive S.val H b
  let inner := H (sequenceFunctionInnerInput b F K derivedK M)
  H (sequenceFunctionOuterInput b F K S M derivedK derivedS inner)

/-- The canonical hash-interface schedule for one `SequenceFunction` call.
It issues between two and four fixed-output-hash calls, according to whether
the key and customization require derivation. -/
def sequenceFunctionStep {L : U128} (b : BlockSize) (K S : ByteString)
    (F : U128) (M : InputSequence)
    (ys : List (HashOutput L)) : List Byte ⊕ HashOutput L :=
  if K.val.length ≤ b.val then
    if S.val.length ≤ b.val then
      match ys with
      | [] =>
          Sum.inl (sequenceFunctionInnerInput b F K (pad K.val b) M)
      | inner :: [] =>
          Sum.inl (sequenceFunctionOuterInput b F K S M
            (pad K.val b) (pad S.val b) inner)
      | _ :: outer :: _ => Sum.inr outer
    else
      match ys with
      | [] => Sum.inl S.val
      | _derivedS :: [] =>
          Sum.inl (sequenceFunctionInnerInput b F K (pad K.val b) M)
      | derivedS :: inner :: [] =>
          Sum.inl (sequenceFunctionOuterInput b F K S M
            (pad K.val b) (pad derivedS.val b) inner)
      | _ :: _ :: outer :: _ => Sum.inr outer
  else
    if S.val.length ≤ b.val then
      match ys with
      | [] => Sum.inl K.val
      | derivedK :: [] =>
          Sum.inl (sequenceFunctionInnerInput b F K (pad derivedK.val b) M)
      | derivedK :: inner :: [] =>
          Sum.inl (sequenceFunctionOuterInput b F K S M
            (pad derivedK.val b) (pad S.val b) inner)
      | _ :: _ :: outer :: _ => Sum.inr outer
    else
      match ys with
      | [] => Sum.inl K.val
      | _derivedK :: [] => Sum.inl S.val
      | derivedK :: _derivedS :: [] =>
          Sum.inl (sequenceFunctionInnerInput b F K (pad derivedK.val b) M)
      | derivedK :: derivedS :: inner :: [] =>
          Sum.inl (sequenceFunctionOuterInput b F K S M
            (pad derivedK.val b) (pad derivedS.val b) inner)
      | _ :: _ :: _ :: outer :: _ => Sum.inr outer

namespace RandomSystemsModel

/-- C2SP's function indicator `F_SEQMAC = 1`. -/
def fSeqMac : U128 := ⟨1, by norm_num [u128Modulus]⟩

/-- Keys accepted by C2SP SequenceMAC: byte strings of at least 32 bytes. -/
abbrev SequenceMACKey := {K : ByteString // 32 ≤ K.val.length}

noncomputable instance instFintypeSequenceMACKey : Fintype SequenceMACKey :=
  Fintype.ofFinite SequenceMACKey

instance instNonemptySequenceMACKey : Nonempty SequenceMACKey :=
  ⟨⟨⟨List.replicate 32 0, by norm_num [u128Modulus]⟩, by simp⟩⟩

/-- Hash-answer histories which can precede a query in the four-call
`SequenceFunction` schedule. -/
abbrev SequenceMACCallHistory (L : U128) :=
  {ys : List (HashOutput L) // ys.length ≤ 3}

noncomputable instance instFintypeSequenceMACCallHistory (L : U128) :
    Fintype (SequenceMACCallHistory L) :=
  (List.finite_length_le (HashOutput L) 3).fintype

/-- Finite witnesses for calls made by one invocation of the schedule. -/
abbrev SequenceMACCallWitness (L : U128) :=
  SequenceMACKey × InputSequence × SequenceMACCallHistory L

/-- The call selected by the canonical `SequenceFunction` schedule at a
finite SequenceMAC witness, if that witness is at a query-producing point. -/
def sequenceFunctionScheduledCall {L : U128} (b : BlockSize)
    (S : ByteString) (w : SequenceMACCallWitness L) : Option (List Byte) :=
  match sequenceFunctionStep b w.1.1 S fSeqMac w.2.1 w.2.2.1 with
  | Sum.inl x => some x
  | Sum.inr _ => none

/-- Compression calls made by one scheduled fixed-output-hash call. -/
def sequenceFunctionHashCallCompressionCost {Block : Type*} {L : U128}
    (codec : MDCodec Block) (b : BlockSize) (S : ByteString)
    (w : SequenceMACCallWitness L) : ℕ :=
  match sequenceFunctionScheduledCall b S w with
  | some x => (codec.blockify x).length
  | none => 0

/-- A finite schedule of at most `Q` canonical fixed-output-hash calls. -/
abbrev SequenceFunctionHashCallSchedule (L : U128) (Q : ℕ) :=
  Fin Q → Option (SequenceMACCallWitness L)

/-- Total compression work of one bounded canonical hash-call schedule. -/
def sequenceFunctionScheduleCompressionCost {Block : Type*} {L : U128}
    (codec : MDCodec Block) (b : BlockSize) (S : ByteString) (Q : ℕ)
    (schedule : SequenceFunctionHashCallSchedule L Q) : ℕ :=
  ∑ i, match schedule i with
    | some w => sequenceFunctionHashCallCompressionCost codec b S w
    | none => 0

/-- Translate a bound of `Q` hash-interface calls and `p` direct primitive
calls into compression-call units. -/
noncomputable def sequenceFunctionCompressionCost {Block : Type*}
    (codec : MDCodec Block) (b : BlockSize) (S : ByteString) (L : U128)
    (Q p : ℕ) : ℕ :=
  p + Finset.sup Finset.univ
    (sequenceFunctionScheduleCompressionCost (L := L) codec b S Q)

end RandomSystemsModel
end SequenceHash

end
