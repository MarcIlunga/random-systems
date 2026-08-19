import SequenceHash.RandomSystems.SequenceMACIndiff

/-!
# SequenceHash and SequenceMAC input-domain separation

Public byte-string facts separating the framed inner and outer hash roles, and
the exact conditional separation of raw derivation calls from those roles.
The raw inputs to long-key and long-customization derivation are not framed,
so their separation is necessarily conditional.
-/

namespace SequenceHash

/-! ## Framed inner/outer roles -/

/-- The padded inner header retains the eight-byte inner-role indicator. -/
@[simp]
theorem take_eight_headerI (b : BlockSize) (F : U128) (K : ByteString) :
    (headerI b F K).take 8 = headerIIndicator := by
  unfold headerI pad
  split
  · simp_all [headerIIndicator]
  · split <;> simp [headerIIndicator]

/-- The padded outer header retains the eight-byte outer-role indicator. -/
@[simp]
theorem take_eight_headerO (b : BlockSize) (F : U128) (S K : ByteString) :
    (headerO b F S K).take 8 = headerOIndicator := by
  unfold headerO pad
  split
  · simp_all [headerOIndicator]
  · split <;> simp [headerOIndicator]

/-- Taking the first eight bytes after appending any suffix still exposes the
inner-role indicator. -/
@[simp]
theorem take_eight_headerI_append (b : BlockSize) (F : U128)
    (K : ByteString) (suffix : List Byte) :
    (headerI b F K ++ suffix).take 8 = headerIIndicator := by
  unfold headerI pad
  split
  · simp_all [headerIIndicator]
  · split <;> simp [headerIIndicator]

/-- Taking the first eight bytes after appending any suffix still exposes the
outer-role indicator. -/
@[simp]
theorem take_eight_headerO_append (b : BlockSize) (F : U128)
    (S K : ByteString) (suffix : List Byte) :
    (headerO b F S K ++ suffix).take 8 = headerOIndicator := by
  unfold headerO pad
  split
  · simp_all [headerOIndicator]
  · split <;> simp [headerOIndicator]

/-- Inner and outer padded headers are unconditionally distinct.  Their
eighth bytes are respectively `73` (`I`) and `79` (`O`). -/
theorem headerI_ne_headerO (b : BlockSize) (F : U128) (S K : ByteString) :
    headerI b F K ≠ headerO b F S K := by
  intro h
  have hIndicators := congrArg (List.take 8) h
  simp only [take_eight_headerI, take_eight_headerO] at hIndicators
  exact (by decide : headerIIndicator ≠ headerOIndicator) hIndicators

/-- The `F = 1` SequenceMAC inner and outer hash inputs are unconditionally
distinct, independently of all derived blocks, messages, and digest values. -/
theorem sequenceMACInnerInput_ne_outerInput {L : U128} (b : BlockSize)
    (S : ByteString) (K : RandomSystemsModel.SequenceMACKey)
    (M N : InputSequence) (derivedKInner derivedSOuter derivedKOuter : List Byte)
    (inner : HashOutput L) :
    RandomSystemsModel.sequenceMACInnerInput b K derivedKInner M ≠
      RandomSystemsModel.sequenceMACOuterInput b S K N derivedSOuter
        derivedKOuter inner := by
  intro h
  have hIndicators := congrArg (List.take 8) h
  apply (by decide : headerIIndicator ≠ headerOIndicator)
  simpa only [RandomSystemsModel.sequenceMACInnerInput,
      RandomSystemsModel.sequenceMACOuterInput, List.append_assoc,
      take_eight_headerI_append, take_eight_headerO_append] using hIndicators

/-- The `F = 2` SequenceHash inner and outer hash inputs are unconditionally
distinct, by the same indicator-byte argument as SequenceMAC. -/
theorem sequenceHashInnerInput_ne_outerInput {L : U128} (b : BlockSize)
    (S : ByteString) (M N : InputSequence) (derivedS : List Byte)
    (inner : HashOutput L) :
    sequenceHashInnerInput b M ≠
      sequenceHashOuterInput b S N derivedS inner := by
  intro h
  have hIndicators := congrArg (List.take 8) h
  apply (by decide : headerIIndicator ≠ headerOIndicator)
  simpa only [sequenceHashInnerInput, sequenceHashOuterInput,
      List.append_assoc, take_eight_headerI_append, take_eight_headerO_append]
      using hIndicators

/-! ## Within-role injectivity -/

/-- The `F = 2` SequenceHash inner input is injective in the item sequence. -/
theorem sequenceHashInnerInput_injective (b : BlockSize) :
    Function.Injective (sequenceHashInnerInput b) := by
  intro M N h
  apply encodeItems_injective
  simpa only [sequenceHashInnerInput, List.append_assoc] using
    List.append_cancel_left h

/-- In the role-separated SequenceMAC schedule, an injective inner-tag
function makes the complete framed outer-call map injective in the item
sequence.  The framing implication is exactly
`sequenceMACSeparatedOuterCall_collision`. -/
theorem sequenceMACSeparatedOuterCall_injective_of_innerTag_injective
    {L : U128} (b : BlockSize) (S : ByteString)
    (a : RandomSystemsModel.SequenceMACSeparatedSeed L)
    (hInner : Function.Injective a.2.2.2) :
    Function.Injective
      (RandomSystemsModel.sequenceMACSeparatedOuterCall b S a) := by
  intro M N hOuter
  by_contra hMN
  exact hMN (hInner
    (RandomSystemsModel.sequenceMACSeparatedOuterCall_collision
      b S a hMN hOuter).2)

/-- Raw-list form of
`sequenceMACSeparatedOuterCall_injective_of_innerTag_injective`: with the
actual separated derived blocks, the SequenceMAC outer input is injective in
the item sequence whenever the inner-tag function is injective. -/
theorem sequenceMACSeparatedOuterInput_injective_of_innerTag_injective
    {L : U128} (b : BlockSize) (S : ByteString)
    (a : RandomSystemsModel.SequenceMACSeparatedSeed L)
    (hInner : Function.Injective a.2.2.2) :
    Function.Injective (fun M =>
      RandomSystemsModel.sequenceMACOuterInput b S a.1 M
        (RandomSystemsModel.sequenceMACSeparatedDerivedS b S a)
        (RandomSystemsModel.sequenceMACSeparatedDerivedK b a) (a.2.2.2 M)) := by
  intro M N hOuter
  apply sequenceMACSeparatedOuterCall_injective_of_innerTag_injective
    b S a hInner
  apply Subtype.ext
  simpa only [RandomSystemsModel.sequenceMACSeparatedOuterCall] using hOuter

/-! ## Raw derivation inputs versus framed roles -/

/-- A raw derivation input is distinct from a SequenceMAC inner input when it
does not begin with the padded inner header block.  This condition is needed:
`derive` hashes the raw input without adding a domain tag. -/
theorem sequenceMACDeriveInput_ne_innerInput_of_not_prefix
    (b : BlockSize) (K : RandomSystemsModel.SequenceMACKey)
    (deriveInput derivedK : List Byte) (M : InputSequence)
    (hPrefix : ¬ List.IsPrefix (headerI b RandomSystemsModel.fSeqMac K.1)
      deriveInput) :
    deriveInput ≠ RandomSystemsModel.sequenceMACInnerInput b K derivedK M := by
  intro h
  apply hPrefix
  rw [h]
  simp [RandomSystemsModel.sequenceMACInnerInput]

/-- A raw derivation input is distinct from a SequenceMAC outer input when it
does not begin with the padded outer header block.  This applies verbatim to
the actual raw inputs `K.val` and `S.val`. -/
theorem sequenceMACDeriveInput_ne_outerInput_of_not_prefix
    {L : U128} (b : BlockSize) (S : ByteString)
    (K : RandomSystemsModel.SequenceMACKey) (deriveInput : List Byte)
    (M : InputSequence) (derivedS derivedK : List Byte) (inner : HashOutput L)
    (hPrefix : ¬ List.IsPrefix
      (headerO b RandomSystemsModel.fSeqMac S K.1) deriveInput) :
    deriveInput ≠
      RandomSystemsModel.sequenceMACOuterInput b S K M derivedS derivedK inner := by
  intro h
  apply hPrefix
  rw [h]
  simp [RandomSystemsModel.sequenceMACOuterInput]

end SequenceHash
