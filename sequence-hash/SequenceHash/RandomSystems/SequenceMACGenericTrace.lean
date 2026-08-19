import SequenceHash.RandomSystems.IdealCompression

/-!
# Canonical SequenceFunction compression traces

This module contains only the compression-trace foundation used by the R4
ideal-compression proof.  It starts from `mdHash` and the canonical
`SequenceFunction`; bad events, equality-on-good, and bad-mass bounds belong
to later modules.
-/

noncomputable section

open scoped BigOperators

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems
open RandomSystems.HTechnique.IdealCompression

universe uState uBlock

/-! ## Merkle--Damgard compression traces -/

/-- One call made by a Merkle--Damgard fold.  The input is exactly the
chaining-state/block pair supplied to the compression function. -/
structure MDCompressionCall (State : Type uState) (Block : Type uBlock) where
  input : State × Block
  output : State
deriving DecidableEq

/-- Compression calls made while folding a block list, starting at `state`. -/
def mdCompressionTraceBlocks {State : Type uState} {Block : Type uBlock}
    (f : Compression State Block) : State → List Block →
      List (MDCompressionCall State Block)
  | _, [] => []
  | state, block :: blocks =>
      { input := (state, block), output := f state block } ::
        mdCompressionTraceBlocks f (f state block) blocks

/-- The compression-call trace of one canonical `mdHash` invocation. -/
def mdCompressionTrace {State : Type uState} {Block : Type uBlock}
    (codec : MDCodec Block) (f : Compression State Block) (iv : State)
    (input : List Byte) : List (MDCompressionCall State Block) :=
  mdCompressionTraceBlocks f iv (codec.blockify input)

@[simp]
theorem mdCompressionTraceBlocks_length {State : Type uState}
    {Block : Type uBlock} (f : Compression State Block) (state : State)
    (blocks : List Block) :
    (mdCompressionTraceBlocks f state blocks).length = blocks.length := by
  induction blocks generalizing state <;> simp [mdCompressionTraceBlocks, *]

/-- One `mdHash` trace entry is produced for every block emitted by the
codec, and for no other object. -/
@[simp]
theorem mdCompressionTrace_length {State : Type uState}
    {Block : Type uBlock} (codec : MDCodec Block)
    (f : Compression State Block) (iv : State) (input : List Byte) :
    (mdCompressionTrace codec f iv input).length =
      (codec.blockify input).length := by
  simp [mdCompressionTrace]

theorem mdCompressionTraceBlocks_reconstruct {State : Type uState}
    {Block : Type uBlock} (f : Compression State Block) (state : State)
    (blocks : List Block) :
    mdIterate f state blocks =
      match (mdCompressionTraceBlocks f state blocks).getLast? with
      | none => state
      | some call => call.output := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block blocks ih =>
      cases blocks with
      | nil => simp [mdIterate, mdCompressionTraceBlocks]
      | cons next rest =>
          simpa [mdIterate, mdCompressionTraceBlocks] using
            ih (f state block)

/-- Reconstruction of the MD result from its trace: an empty trace returns
the IV, while a nonempty trace returns its last compression output. -/
theorem mdCompressionTrace_reconstruct {State : Type uState}
    {Block : Type uBlock} (codec : MDCodec Block)
    (f : Compression State Block) (iv : State) (input : List Byte) :
    mdHash codec f iv input =
      match (mdCompressionTrace codec f iv input).getLast? with
      | none => iv
      | some call => call.output := by
  exact mdCompressionTraceBlocks_reconstruct f iv (codec.blockify input)

/-- In the nonempty case, the final compression output is the hash output. -/
theorem mdCompressionTrace_final_output {State : Type uState}
    {Block : Type uBlock} (codec : MDCodec Block)
    (f : Compression State Block) (iv : State) (input : List Byte)
    (call : MDCompressionCall State Block)
    (hlast : (mdCompressionTrace codec f iv input).getLast? = some call) :
    call.output = mdHash codec f iv input := by
  rw [mdCompressionTrace_reconstruct, hlast]

theorem mdCompressionTrace_nonempty_iff {State : Type uState}
    {Block : Type uBlock} (codec : MDCodec Block)
    (f : Compression State Block) (iv : State) (input : List Byte) :
    mdCompressionTrace codec f iv input ≠ [] ↔
      codec.blockify input ≠ [] := by
  simp only [← List.length_pos_iff_ne_nil, mdCompressionTrace_length]

/-! ## Role-tagged SequenceFunction traces -/

/-- The four semantic roles of a canonical SequenceFunction compression
call.  Short key/customization derivations have no calls in their roles. -/
inductive SequenceFunctionCompressionRole where
  | deriveKey
  | deriveCustomization
  | inner
  | outer
deriving DecidableEq, Fintype

/-- Attach a construction role to every entry of an MD trace. -/
def tagMDCompressionTrace {State : Type uState} {Block : Type uBlock}
    (role : SequenceFunctionCompressionRole)
    (trace : List (MDCompressionCall State Block)) :
    List (TraceEntry SequenceFunctionCompressionRole State Block) :=
  trace.map fun call =>
    { role := role, input := call.input, output := call.output }

@[simp]
theorem tagMDCompressionTrace_length {State : Type uState}
    {Block : Type uBlock} (role : SequenceFunctionCompressionRole)
    (trace : List (MDCompressionCall State Block)) :
    (tagMDCompressionTrace role trace).length = trace.length := by
  simp [tagMDCompressionTrace]

/-- The canonical role-tagged compression trace of
`SequenceFunction(MD[h],K,S,1;M)`.  It concatenates, in execution order, the
optional raw-key derivation, optional customization derivation, inner hash,
and outer hash.  All byte strings are supplied by the canonical
`sequenceFunctionInnerInput`/`sequenceFunctionOuterInput` constructors. -/
def sequenceFunctionCompressionTrace {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    List (TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block) :=
  let H := mdHash model.codec h model.iv
  let derivedK := derive K.1.val H b
  let derivedS := derive S.val H b
  let innerInput := sequenceFunctionInnerInput b fSeqMac K.1 derivedK M
  let inner := H innerInput
  let outerInput :=
    sequenceFunctionOuterInput b fSeqMac K.1 S M derivedK derivedS inner
  (if K.1.val.length ≤ b.val then [] else
      tagMDCompressionTrace .deriveKey
        (mdCompressionTrace model.codec h model.iv K.1.val)) ++
    (if S.val.length ≤ b.val then [] else
      tagMDCompressionTrace .deriveCustomization
        (mdCompressionTrace model.codec h model.iv S.val)) ++
    tagMDCompressionTrace .inner
      (mdCompressionTrace model.codec h model.iv innerInput) ++
    tagMDCompressionTrace .outer
      (mdCompressionTrace model.codec h model.iv outerInput)

/-- Exact block count of the canonical trace. -/
theorem sequenceFunctionCompressionTrace_length {Block : Type uBlock}
    {L : U128} (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    (sequenceFunctionCompressionTrace model b S h K M).length =
      (if K.1.val.length ≤ b.val then 0
        else (model.codec.blockify K.1.val).length) +
      (if S.val.length ≤ b.val then 0
        else (model.codec.blockify S.val).length) +
      (model.codec.blockify
        (sequenceFunctionInnerInput b fSeqMac K.1
          (derive K.1.val (mdHash model.codec h model.iv) b) M)).length +
      (model.codec.blockify
        (sequenceFunctionOuterInput b fSeqMac K.1 S M
          (derive K.1.val (mdHash model.codec h model.iv) b)
          (derive S.val (mdHash model.codec h model.iv) b)
          (mdHash model.codec h model.iv
            (sequenceFunctionInnerInput b fSeqMac K.1
              (derive K.1.val (mdHash model.codec h model.iv) b) M)))).length := by
  by_cases hK : K.1.val.length ≤ b.val <;>
    by_cases hS : S.val.length ≤ b.val <;>
    simp [sequenceFunctionCompressionTrace, hK, hS, Nat.add_assoc]

/-! ### The canonical four-call schedule witnesses the frozen cost bound -/

/-- The at-most-four fixed-output-hash calls underlying the compression
trace, represented in the finite schedule type used by
`sequenceFunctionCompressionCost`. -/
def sequenceFunctionCompressionSchedule {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    SequenceFunctionHashCallSchedule L 4 :=
  let H := mdHash model.codec h model.iv
  let hashK := H K.1.val
  let hashS := H S.val
  let derivedK := derive K.1.val H b
  let derivedS := derive S.val H b
  let inner := H (sequenceFunctionInnerInput b fSeqMac K.1 derivedK M)
  if K.1.val.length ≤ b.val then
    if S.val.length ≤ b.val then
      ![some (K, M, ⟨[], by simp⟩),
        some (K, M, ⟨[inner], by simp⟩), none, none]
    else
      ![some (K, M, ⟨[], by simp⟩),
        some (K, M, ⟨[hashS], by simp⟩),
        some (K, M, ⟨[hashS, inner], by simp⟩), none]
  else
    if S.val.length ≤ b.val then
      ![some (K, M, ⟨[], by simp⟩),
        some (K, M, ⟨[hashK], by simp⟩),
        some (K, M, ⟨[hashK, inner], by simp⟩), none]
    else
      ![some (K, M, ⟨[], by simp⟩),
        some (K, M, ⟨[hashK], by simp⟩),
        some (K, M, ⟨[hashK, hashS], by simp⟩),
        some (K, M, ⟨[hashK, hashS, inner], by simp⟩)]

/-- The concrete schedule cost is exactly the role-tagged trace length. -/
theorem sequenceFunctionCompressionSchedule_cost_eq_trace_length
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    sequenceFunctionScheduleCompressionCost model.codec b S 4
        (sequenceFunctionCompressionSchedule model b S h K M) =
      (sequenceFunctionCompressionTrace model b S h K M).length := by
  by_cases hK : K.1.val.length ≤ b.val <;>
    by_cases hS : S.val.length ≤ b.val <;>
    simp [sequenceFunctionCompressionSchedule,
      sequenceFunctionScheduleCompressionCost,
      sequenceFunctionHashCallCompressionCost,
      sequenceFunctionScheduledCall, sequenceFunctionStep,
      sequenceFunctionCompressionTrace_length, derive, hK, hS,
      Fin.sum_univ_succ, Nat.add_assoc]

/-- The supremum used by the facade really bounds the canonical compression
trace; this is the bridge from concrete traces to `sequenceFunctionEvalCost`. -/
theorem sequenceFunctionCompressionTrace_length_le_evalCost
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) {users : ℕ}
    (i : Fin users) :
    (sequenceFunctionCompressionTrace model b S h K M).length ≤
      sequenceFunctionEvalCost model b S (i, M) := by
  rw [sequenceFunctionEvalCost, sequenceFunctionCompressionCost,
    Nat.zero_add, ← sequenceFunctionCompressionSchedule_cost_eq_trace_length]
  exact Finset.le_sup (Finset.mem_univ
    (sequenceFunctionCompressionSchedule model b S h K M))

/-- A frozen `SequenceFunctionTraceBound` bounds every concrete canonical
trace by the public padding length `lambda`. -/
theorem sequenceFunctionCompressionTrace_length_le_traceBound
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString} {lambda rK rS users : ℕ}
    (bound : SequenceFunctionTraceBound model b S lambda rK rS)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) (i : Fin users) :
    (sequenceFunctionCompressionTrace model b S h K M).length ≤ lambda := by
  exact (sequenceFunctionCompressionTrace_length_le_evalCost
    model b S h K M i).trans (bound.evalCost_apply_le (i, M))

/-! ### Padding into the generic reveal carrier -/

/-- Pad a finite list of compression calls into the facade's fixed-size
trace carrier.  Entries beyond the list are `none`. -/
def padCompressionTrace {Role : Type*} {State : Type uState}
    {Block : Type uBlock} (lambda : ℕ)
    (trace : List (TraceEntry Role State Block)) :
    EvalTrace Role State Block lambda :=
  fun i => if hi : i.val < trace.length then some (trace.get ⟨i.val, hi⟩) else none

@[simp]
theorem padCompressionTrace_eq_some_of_lt {Role : Type*}
    {State : Type uState} {Block : Type uBlock} {lambda : ℕ}
    (trace : List (TraceEntry Role State Block)) (i : Fin lambda)
    (hi : i.val < trace.length) :
    padCompressionTrace lambda trace i = some (trace.get ⟨i.val, hi⟩) := by
  simp [padCompressionTrace, hi]

@[simp]
theorem padCompressionTrace_eq_none_of_length_le {Role : Type*}
    {State : Type uState} {Block : Type uBlock} {lambda : ℕ}
    (trace : List (TraceEntry Role State Block)) (i : Fin lambda)
    (hi : trace.length ≤ i.val) :
    padCompressionTrace lambda trace i = none := by
  simp [padCompressionTrace, Nat.not_lt.mpr hi]

/-- Every canonical entry survives padding under the frozen trace bound. -/
theorem padCompressionTrace_castLE_traceBound
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString} {lambda rK rS users : ℕ}
    (bound : SequenceFunctionTraceBound model b S lambda rK rS)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) (user : Fin users)
    (i : Fin (sequenceFunctionCompressionTrace model b S h K M).length) :
    padCompressionTrace lambda
        (sequenceFunctionCompressionTrace model b S h K M)
        (Fin.castLE
          (sequenceFunctionCompressionTrace_length_le_traceBound
            bound h K M user) i) =
      some ((sequenceFunctionCompressionTrace model b S h K M).get i) := by
  simp [padCompressionTrace]

/-! ## The output-backed codec condition -/

/-- Precise codec premise needed to turn a nonempty byte string into at
least one compression call. -/
def MDCodecBlockifyNonemptyInput {Block : Type uBlock}
    (codec : MDCodec Block) : Prop :=
  ∀ input : List Byte, input ≠ [] → codec.blockify input ≠ []

/-- The explicit R4 assumption that every canonical outer call has at least
one compression block.  It is intentionally separate from role separation
and from all future bad-event definitions. -/
def SequenceFunctionOutputCompressionBacked {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) : Prop :=
  ∀ (K : SequenceMACKey) (M : InputSequence)
      (derivedK derivedS : List Byte) (inner : HashOutput L),
    model.codec.blockify
      (sequenceFunctionOuterInput b fSeqMac K.1 S M
        derivedK derivedS inner) ≠ []

/-- Output backing witnesses an actual compression block, so the primitive
query carrier is nonempty. -/
theorem SequenceFunctionOutputCompressionBacked.nonemptyBlock
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (backed : SequenceFunctionOutputCompressionBacked model b S) :
    Nonempty Block := by
  let blocks := model.codec.blockify
    (sequenceFunctionOuterInput b fSeqMac
      (Classical.arbitrary SequenceMACKey).1 S
      (Classical.arbitrary InputSequence) [] [] model.iv)
  exact ⟨blocks.getLast (backed _ _ [] [] model.iv)⟩

/-- Canonical outer inputs are nonempty because `headerO` begins with the
nonempty `SEQHSH_O` indicator. -/
theorem pad_ne_nil (input : List Byte) (b : BlockSize) :
    pad input b ≠ [] := by
  cases input with
  | nil => simp [pad, Nat.ne_of_gt b.property]
  | cons byte rest =>
      simp only [pad, List.length_cons]
      split
      · omega
      · split <;> simp

theorem sequenceFunctionOuterInput_nonempty {L : U128}
    (b : BlockSize) (S : ByteString) (K : SequenceMACKey)
    (M : InputSequence) (derivedK derivedS : List Byte)
    (inner : HashOutput L) :
    sequenceFunctionOuterInput b fSeqMac K.1 S M
      derivedK derivedS inner ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  have hheader : 0 < (headerO b fSeqMac S K.1).length :=
    List.length_pos_iff_ne_nil.mpr (pad_ne_nil _ b)
  simp only [sequenceFunctionOuterInput, List.length_append,
    List.length_nil] at hlength
  omega

/-- Any codec that blockifies every nonempty byte input into at least one
block satisfies the output-backed assumption. -/
theorem SequenceFunctionOutputCompressionBacked.of_blockifyNonemptyInput
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (hcodec : MDCodecBlockifyNonemptyInput model.codec) :
    SequenceFunctionOutputCompressionBacked model b S := by
  intro K M derivedK derivedS inner
  exact hcodec _
    (sequenceFunctionOuterInput_nonempty b S K M derivedK derivedS inner)

/-- Output backing makes the final outer MD trace nonempty. -/
theorem sequenceFunctionOuterCompressionTrace_nonempty
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    let H := mdHash model.codec h model.iv
    let derivedK := derive K.1.val H b
    let derivedS := derive S.val H b
    let inner := H (sequenceFunctionInnerInput b fSeqMac K.1 derivedK M)
    mdCompressionTrace model.codec h model.iv
      (sequenceFunctionOuterInput b fSeqMac K.1 S M
        derivedK derivedS inner) ≠ [] := by
  simp only
  apply (mdCompressionTrace_nonempty_iff _ _ _ _).2
  exact backed K M _ _ _

/-- Under output backing, the last role-tagged compression entry is an outer
call and its output is exactly the canonical real `Eval` reply. -/
theorem sequenceFunctionCompressionTrace_final_output
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    ∃ input : HashOutput L × Block,
      (sequenceFunctionCompressionTrace model b S h K M).getLast? =
        some ⟨SequenceFunctionCompressionRole.outer, input,
          sequenceFunctionICEval model b S h K M⟩ := by
  let H := mdHash model.codec h model.iv
  let derivedK := derive K.1.val H b
  let derivedS := derive S.val H b
  let innerInput := sequenceFunctionInnerInput b fSeqMac K.1 derivedK M
  let inner := H innerInput
  let outerInput :=
    sequenceFunctionOuterInput b fSeqMac K.1 S M derivedK derivedS inner
  let outerTrace := mdCompressionTrace model.codec h model.iv outerInput
  have hne : outerTrace ≠ [] := by
    exact (mdCompressionTrace_nonempty_iff model.codec h model.iv outerInput).2
      (backed K M derivedK derivedS inner)
  let last := outerTrace.getLast hne
  have hlast : outerTrace.getLast? = some last :=
    List.getLast?_eq_getLast_of_ne_nil hne
  have houtput : last.output = H outerInput :=
    mdCompressionTrace_final_output model.codec h model.iv outerInput last hlast
  have htag : tagMDCompressionTrace SequenceFunctionCompressionRole.outer
      outerTrace ≠ [] := by
    simp [tagMDCompressionTrace, hne]
  refine ⟨last.input, ?_⟩
  rw [show sequenceFunctionCompressionTrace model b S h K M =
      ((if K.1.val.length ≤ b.val then [] else
          tagMDCompressionTrace .deriveKey
            (mdCompressionTrace model.codec h model.iv K.1.val)) ++
        (if S.val.length ≤ b.val then [] else
          tagMDCompressionTrace .deriveCustomization
            (mdCompressionTrace model.codec h model.iv S.val)) ++
        tagMDCompressionTrace .inner
          (mdCompressionTrace model.codec h model.iv innerInput)) ++
        tagMDCompressionTrace .outer outerTrace by
      rfl]
  rw [List.getLast?_append_of_ne_nil _ htag]
  simp [tagMDCompressionTrace, hlast, houtput, sequenceFunctionICEval,
    sequenceFunction, H, derivedK, derivedS, innerInput, inner, outerInput]

end RandomSystemsModel
end SequenceHash
