import Mathlib.Data.Nat.Digits.Lemmas

/-!
# C2SP SequenceHash encoding

This module formalizes the byte-oriented, 128-bit length-prefix encoding from
the C2SP SequenceHash v0.1.0 specification.  It is deliberately independent of
the RandomSystems and AbstractCrypto libraries.

The central result is `encodeItems_injective`: concatenating the framed items
has a unique parse, including empty items. Decoder and recursive parsing facts
are proof-local implementation details rather than a second public API.
-/

namespace SequenceHash

/-- One byte, represented by its value in `[0, 256)`. -/
abbrev Byte := Fin 256

/-- The modulus of a 128-bit unsigned integer, written in the byte-oriented
form used by the specification. -/
def u128Modulus : Nat := 256 ^ 16

/-- An unsigned 128-bit integer. -/
abbrev U128 := Fin u128Modulus

/-- A byte string accepted by the C2SP encoding.  The specification limits
each item to at most `2^128 - 1` bytes. -/
abbrev ByteString := {xs : List Byte // xs.length < u128Modulus}

/-- A sequence accepted by `SequenceFunction`.  Its number of items must also
fit in the 128-bit item-count field. -/
abbrev InputSequence := {xs : List ByteString // xs.length < u128Modulus}

/-- The specification's 16-byte, least-significant-byte-first encoding. -/
def encodeLSBF (n : U128) : List Byte :=
  (Nat.digitsAppend 256 16 n.val).map (Fin.ofNat 256)

/-- Reading the byte values of `encodeLSBF` recovers Mathlib's fixed-width
base-256 digit list. -/
theorem encodeLSBF_map_val (n : U128) :
    (encodeLSBF n).map (fun b => b.val) = Nat.digitsAppend 256 16 n.val := by
  simp only [encodeLSBF, List.map_map]
  have h :
      List.map ((fun b : Byte => b.val) ∘ Fin.ofNat 256)
          (Nat.digitsAppend 256 16 n.val) =
        List.map id (Nat.digitsAppend 256 16 n.val) := by
    apply List.map_congr_left
    intro d hd
    simp only [Function.comp_apply, Fin.val_ofNat, id_eq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_mem_digitsAppend (by decide) 16 d hd)
  simpa only [List.map_id] using h

/-- `EncodeLSBF` always emits exactly 16 bytes. -/
@[simp]
theorem length_encodeLSBF (n : U128) : (encodeLSBF n).length = 16 := by
  simp only [encodeLSBF, List.length_map]
  exact Nat.length_digitsAppend (by decide) 16 n.isLt

/-- Interpret a little-endian byte list as a natural number.  This is total;
only its action on 16-byte encodings is used as a decoder. -/
def decodeLSBF (xs : List Byte) : Nat :=
  Nat.ofDigits 256 (xs.map fun b => b.val)

/-- The numerical decoder is a left inverse of `encodeLSBF`. -/
@[simp]
theorem decodeLSBF_encodeLSBF (n : U128) :
    decodeLSBF (encodeLSBF n) = n.val := by
  rw [decodeLSBF, encodeLSBF_map_val]
  exact (Nat.setInvOn_digitsAppend_ofDigits (b := 256) (by decide) 16).2 n.isLt

/-- The concrete 16-byte little-endian encoding is injective. -/
theorem encodeLSBF_injective : Function.Injective encodeLSBF := by
  intro a b h
  apply Fin.ext
  simpa only [decodeLSBF_encodeLSBF] using congrArg decodeLSBF h

/-- The specification's most-significant-byte-first representation is the
reverse of the little-endian representation. -/
def encodeMSBF (n : U128) : List Byte :=
  (encodeLSBF n).reverse

/-- `EncodeMSBF` always emits exactly 16 bytes. -/
@[simp]
theorem length_encodeMSBF (n : U128) : (encodeMSBF n).length = 16 := by
  simp [encodeMSBF]

/-- The concrete 16-byte big-endian encoding is injective. -/
theorem encodeMSBF_injective : Function.Injective encodeMSBF := by
  intro a b h
  exact encodeLSBF_injective (List.reverse_injective h)

/-- C2SP `Encode(x) = EncodeLSBF(len(x)) || x`. -/
def encode (x : ByteString) : List Byte :=
  encodeLSBF ⟨x.val.length, x.property⟩ ++ x.val

/-- A single framed item is never the empty byte string, including when its
payload is empty. -/
theorem encode_ne_nil (x : ByteString) : encode x ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [encode] at this

/-- Concatenate the C2SP encodings of a sequence of byte strings. -/
def encodeSequence : List ByteString → List Byte
  | [] => []
  | x :: xs => encode x ++ encodeSequence xs

@[simp]
theorem encodeSequence_nil : encodeSequence [] = [] := rfl

@[simp]
theorem encodeSequence_cons (x : ByteString) (xs : List ByteString) :
    encodeSequence (x :: xs) = encode x ++ encodeSequence xs := rfl

/-- A nonempty sequence has a nonempty encoding. -/
theorem encodeSequence_cons_ne_nil (x : ByteString) (xs : List ByteString) :
    encodeSequence (x :: xs) ≠ [] :=
  List.append_ne_nil_of_left_ne_nil (encode_ne_nil x) _

/-- The C2SP sequence framing has a unique parse.  In particular, neither
empty items nor boundaries between adjacent items can be confused. -/
theorem encodeSequence_injective : Function.Injective encodeSequence := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => exact False.elim (encodeSequence_cons_ne_nil y ys h.symm)
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => exact False.elim (encodeSequence_cons_ne_nil x xs h)
      | cons y ys =>
          simp only [encodeSequence_cons, encode, List.append_assoc] at h
          have hCode :
              encodeLSBF ⟨x.val.length, x.property⟩ =
                encodeLSBF ⟨y.val.length, y.property⟩ :=
            List.append_inj_left h (by simp)
          have hLength : x.val.length = y.val.length := by
            exact congrArg Fin.val (encodeLSBF_injective hCode)
          have hRest : x.val ++ encodeSequence xs = y.val ++ encodeSequence ys := by
            rw [hCode] at h
            exact List.append_cancel_left h
          have hData : x.val = y.val :=
            List.append_inj_left hRest hLength
          have hTail : encodeSequence xs = encodeSequence ys := by
            rw [hData] at hRest
            exact List.append_cancel_left hRest
          have hHead : x = y := Subtype.ext hData
          rw [hHead, ih hTail]

/-- Serialize the items of an input satisfying the specification's item-count
bound.  The outer SequenceHash call encodes the item count separately. -/
def encodeItems (xs : InputSequence) : List Byte :=
  encodeSequence xs.val

/-- The bounded, specification-facing sequence encoder is injective. -/
theorem encodeItems_injective : Function.Injective encodeItems := by
  intro xs ys h
  exact Subtype.ext (encodeSequence_injective h)

end SequenceHash
