import SequenceHash.Encoding

/-!
# C2SP SequenceHash: pure construction and collision accounting

This is the Mathlib-only C2SP SequenceHash v0.1.0 object. The hash output
length is carried by its type, and all specification inputs carry the C2SP
128-bit length bound.

The headline theorem is `sequenceHash_collision_of_distinct_inputs`: equal
SequenceHash outputs for distinct customization/sequence pairs give an actual
collision of the underlying hash at the outer calls, the inner calls, or the
customization-derivation calls. This is the strongest unconditional statement
available: a finite-output hash itself cannot be collision-free.

Following the development discipline of `RandomSystems.CBCMAC`, the
construction is stated first and the obligations forced by the headline
theorem remain local to its proof.
-/

namespace SequenceHash

/-- A positive hash block size, in bytes. -/
abbrev BlockSize := {b : Nat // 0 < b}

/-- A digest whose byte length is the fixed 128-bit value `L`. -/
abbrev HashOutput (L : U128) := {out : List Byte // out.length = L.val}

/-- The pure fixed-output hash interface used by the C2SP construction. -/
abbrev FixedHash (L : U128) := List Byte → HashOutput L

/-- C2SP `Pad(x, b)`: right-pad to the smallest positive multiple of `b`. -/
def pad (x : List Byte) (b : BlockSize) : List Byte :=
  if x.length = 0 then
    List.replicate b.val 0
  else if x.length % b.val = 0 then
    x
  else
    x ++ List.replicate (b.val - x.length % b.val) 0

/-- C2SP `Derive(I, H, b)`. -/
def derive {L : U128} (I : List Byte) (H : FixedHash L) (b : BlockSize) :
    List Byte :=
  if I.length ≤ b.val then pad I b else pad (H I).val b

/-- The eight-byte ASCII domain indicator `SEQHSH_I`. -/
def headerIIndicator : List Byte := [83, 69, 81, 72, 83, 72, 95, 73]

/-- The eight-byte ASCII domain indicator `SEQHSH_O`. -/
def headerOIndicator : List Byte := [83, 69, 81, 72, 83, 72, 95, 79]

/-- C2SP `HeaderI(b, F, K)`. -/
def headerI (b : BlockSize) (F : U128) (K : ByteString) : List Byte :=
  pad
    (headerIIndicator ++ encodeMSBF F ++
      encodeMSBF ⟨K.val.length, K.property⟩)
    b

/-- C2SP `HeaderO(b, F, S, K)`. -/
def headerO (b : BlockSize) (F : U128) (S K : ByteString) : List Byte :=
  pad
    (headerOIndicator ++ encodeMSBF F ++
      encodeMSBF ⟨S.val.length, S.property⟩ ++
      encodeMSBF ⟨K.val.length, K.property⟩)
    b

/-- The empty key fixed by SequenceHash. -/
def emptyByteString : ByteString := ⟨[], by simp [u128Modulus]⟩

/-- C2SP's function indicator `F_SEQHSH = 2`. -/
def fSeqHsh : U128 := ⟨2, by norm_num [u128Modulus]⟩

/-- The exact inner-hash input of C2SP `SequenceHash`. -/
def sequenceHashInnerInput (b : BlockSize) (M : InputSequence) : List Byte :=
  headerI b fSeqHsh emptyByteString ++
    pad emptyByteString.val b ++
    encodeItems M

/-- Assemble the exact outer-hash input from the derived customization block
and inner digest. These are precisely the two values obtained from the
preceding hash calls. -/
def sequenceHashOuterInput {L : U128} (b : BlockSize) (S : ByteString)
    (M : InputSequence) (derivedS : List Byte) (inner : HashOutput L) :
    List Byte :=
  headerO b fSeqHsh S emptyByteString ++
    derivedS ++
    pad emptyByteString.val b ++
    encodeMSBF ⟨M.val.length, M.property⟩ ++
    encodeMSBF L ++
    inner.val

/-- C2SP `SequenceHash(H, S; M₁, ..., Mₙ)`. -/
def sequenceHash {L : U128} (b : BlockSize) (H : FixedHash L)
    (S : ByteString) (M : InputSequence) : HashOutput L :=
  let inner := H (sequenceHashInnerInput b M)
  H (sequenceHashOuterInput b S M (derive S.val H b) inner)

/-- An actual collision of `H` on two distinct byte strings. -/
def HashCollision {L : U128} (H : FixedHash L) (x y : List Byte) : Prop :=
  x ≠ y ∧ H x = H y

/-- **Pure SequenceHash ambiguity/collision theorem.** Distinct accepted
inputs with equal outputs force a collision at actual calls made by the
construction: the outer calls, the inner calls, or (when both customization
strings are long) the two derivation calls. -/
theorem sequenceHash_collision_of_distinct_inputs {L : U128} (b : BlockSize)
    (H : FixedHash L) {S T : ByteString} {M N : InputSequence}
    (hInput : (S, M) ≠ (T, N))
    (hOutput : sequenceHash b H S M = sequenceHash b H T N) :
    let innerM := sequenceHashInnerInput b M
    let innerN := sequenceHashInnerInput b N
    let outerM := sequenceHashOuterInput b S M (derive S.val H b) (H innerM)
    let outerN := sequenceHashOuterInput b T N (derive T.val H b) (H innerN)
    HashCollision H outerM outerN ∨
      HashCollision H innerM innerN ∨
      (b.val < S.val.length ∧ b.val < T.val.length ∧
        HashCollision H S.val T.val) := by
  dsimp only
  let innerM := sequenceHashInnerInput b M
  let innerN := sequenceHashInnerInput b N
  let outerM := sequenceHashOuterInput b S M (derive S.val H b) (H innerM)
  let outerN := sequenceHashOuterInput b T N (derive T.val H b) (H innerN)
  by_cases hOuter : outerM = outerN
  · have pad_take (x : List Byte) : (pad x b).take x.length = x := by
      unfold pad
      by_cases hx : x.length = 0
      · have hxnil : x = [] := List.eq_nil_of_length_eq_zero hx
        subst x
        simp
      · by_cases hmod : x.length % b.val = 0
        · simp [hx, hmod]
        · simp [hx, hmod]
    have pad_length_of_length_eq {x y : List Byte} (hxy : x.length = y.length) :
        (pad x b).length = (pad y b).length := by
      by_cases hx : x.length = 0
      · have hy : y.length = 0 := by omega
        rw [List.eq_nil_of_length_eq_zero hx, List.eq_nil_of_length_eq_zero hy]
      · have hy : y.length ≠ 0 := by omega
        by_cases hmod : y.length % b.val = 0 <;>
          simp [pad, hy, hxy, hmod]
    have hHeaderLength (U : ByteString) :
        (headerO b fSeqHsh U emptyByteString).length =
          (headerO b fSeqHsh S emptyByteString).length := by
      unfold headerO
      apply pad_length_of_length_eq
      simp
    have hHeader :
        headerO b fSeqHsh S emptyByteString =
          headerO b fSeqHsh T emptyByteString := by
      unfold outerM outerN sequenceHashOuterInput at hOuter
      simp only [List.append_assoc] at hOuter
      exact List.append_inj_left hOuter (hHeaderLength T).symm
    have hRawHeader :
        headerOIndicator ++ encodeMSBF fSeqHsh ++
            encodeMSBF ⟨S.val.length, S.property⟩ ++
            encodeMSBF ⟨emptyByteString.val.length, emptyByteString.property⟩ =
          headerOIndicator ++ encodeMSBF fSeqHsh ++
            encodeMSBF ⟨T.val.length, T.property⟩ ++
            encodeMSBF ⟨emptyByteString.val.length, emptyByteString.property⟩ := by
      unfold headerO at hHeader
      let rawS := headerOIndicator ++ encodeMSBF fSeqHsh ++
        encodeMSBF ⟨S.val.length, S.property⟩ ++
        encodeMSBF ⟨emptyByteString.val.length, emptyByteString.property⟩
      let rawT := headerOIndicator ++ encodeMSBF fSeqHsh ++
        encodeMSBF ⟨T.val.length, T.property⟩ ++
        encodeMSBF ⟨emptyByteString.val.length, emptyByteString.property⟩
      change pad rawS b = pad rawT b at hHeader
      change rawS = rawT
      calc
        rawS = (pad rawS b).take rawS.length := (pad_take rawS).symm
        _ = (pad rawT b).take rawS.length := congrArg (fun xs => xs.take rawS.length) hHeader
        _ = (pad rawT b).take rawT.length := by simp [rawS, rawT]
        _ = rawT := pad_take rawT
    have hLength : S.val.length = T.val.length := by
      simp only [List.append_assoc] at hRawHeader
      have h := List.append_cancel_left (List.append_cancel_left hRawHeader)
      have hCode :
          encodeMSBF ⟨S.val.length, S.property⟩ =
            encodeMSBF ⟨T.val.length, T.property⟩ :=
        List.append_inj_left h (by simp)
      exact congrArg Fin.val (encodeMSBF_injective hCode)
    have hDeriveLength :
        (derive S.val H b).length = (derive T.val H b).length := by
      unfold derive
      by_cases hShort : S.val.length ≤ b.val
      · have hShortT : T.val.length ≤ b.val := by omega
        simp only [hShort, hShortT, if_pos]
        exact pad_length_of_length_eq hLength
      · have hShortT : ¬ T.val.length ≤ b.val := by omega
        simp only [hShort, hShortT, if_false]
        apply pad_length_of_length_eq
        exact (H S.val).property.trans (H T.val).property.symm
    have hAfterHeader :
        derive S.val H b ++
            pad emptyByteString.val b ++
            encodeMSBF ⟨M.val.length, M.property⟩ ++
            encodeMSBF L ++ (H innerM).val =
          derive T.val H b ++
            pad emptyByteString.val b ++
            encodeMSBF ⟨N.val.length, N.property⟩ ++
            encodeMSBF L ++ (H innerN).val := by
      unfold outerM outerN sequenceHashOuterInput at hOuter
      simp only [List.append_assoc] at hOuter ⊢
      rw [hHeader] at hOuter
      exact List.append_cancel_left hOuter
    have hDerive : derive S.val H b = derive T.val H b :=
      List.append_inj_left (by simpa only [List.append_assoc] using hAfterHeader) hDeriveLength
    by_cases hST : S = T
    · subst T
      right
      left
      have hMN : M ≠ N := by
        intro h
        exact hInput (by simp [h])
      refine ⟨?_, ?_⟩
      · change sequenceHashInnerInput b M ≠ sequenceHashInnerInput b N
        intro hInner
        apply hMN
        apply encodeItems_injective
        unfold sequenceHashInnerInput at hInner
        simp only [List.append_assoc] at hInner
        exact List.append_cancel_left (List.append_cancel_left hInner)
      · rw [hDerive] at hAfterHeader
        simp only [List.append_assoc] at hAfterHeader
        have hAfterDerive := List.append_cancel_left hAfterHeader
        have hAfterKey := List.append_cancel_left hAfterDerive
        have hCount :
            encodeMSBF ⟨M.val.length, M.property⟩ =
              encodeMSBF ⟨N.val.length, N.property⟩ :=
          List.append_inj_left hAfterKey (by simp)
        rw [hCount] at hAfterKey
        have hAfterCount := List.append_cancel_left hAfterKey
        have hDigest := List.append_cancel_left hAfterCount
        exact Subtype.ext hDigest
    · right
      right
      have hLongS : b.val < S.val.length := by
        by_contra h
        have hShortS : S.val.length ≤ b.val := by omega
        have hShortT : T.val.length ≤ b.val := by omega
        unfold derive at hDerive
        simp only [hShortS, hShortT, if_pos] at hDerive
        apply hST
        apply Subtype.ext
        calc
          S.val = (pad S.val b).take S.val.length := (pad_take S.val).symm
          _ = (pad T.val b).take S.val.length :=
            congrArg (fun xs => xs.take S.val.length) hDerive
          _ = (pad T.val b).take T.val.length := by rw [hLength]
          _ = T.val := pad_take T.val
      have hLongT : b.val < T.val.length := by omega
      have hSTval : S.val ≠ T.val := fun h => hST (Subtype.ext h)
      refine ⟨hLongS, hLongT, hSTval, ?_⟩
      unfold derive at hDerive
      simp only [show ¬ S.val.length ≤ b.val by omega,
        show ¬ T.val.length ≤ b.val by omega, if_false] at hDerive
      apply Subtype.ext
      have hHashLength : (H S.val).val.length = (H T.val).val.length :=
        (H S.val).property.trans (H T.val).property.symm
      calc
        (H S.val).val = (pad (H S.val).val b).take (H S.val).val.length :=
          (pad_take (H S.val).val).symm
        _ = (pad (H T.val).val b).take (H S.val).val.length :=
          congrArg (fun xs => xs.take (H S.val).val.length) hDerive
        _ = (pad (H T.val).val b).take (H T.val).val.length := by rw [hHashLength]
        _ = (H T.val).val := pad_take (H T.val).val
  · left
    refine ⟨hOuter, ?_⟩
    simpa only [sequenceHash, innerM, innerN, outerM, outerN] using hOutput

end SequenceHash
