import SequenceHash.Encoding

/-!
# Merkle–Damgård model

This is the byte-to-block codec and fold model used by the SequenceMAC PRF
development.  It is independent of any particular compression function or MD
padding algorithm: a codec records the chosen native padding, its full-block
serialization, and the construction-facing faithfulness needed to embed C2SP
input sequences into compression-block strings.
-/

namespace SequenceHash

/-- A Merkle–Damgård compression transition.  In the R2 model this is
`f : C → B → C`: the current chaining value is the compression key. -/
abbrev Compression (State Block : Type*) := State → Block → State

/-- An abstract codec from byte strings to compression blocks.

`padding` is the hash's native MD padding/strengthening, while `encodeBlock`
exposes enough of an abstract `Block` to state that `blockify` emits complete
blocks and realizes that padding byte-for-byte. -/
structure MDCodec (Block : Type*) where
  /-- The native compression-block length in bytes. -/
  blockSize : ℕ
  /-- Compression blocks are nonempty. -/
  blockSize_pos : 0 < blockSize
  /-- Byte serialization of an abstract compression block. -/
  encodeBlock : Block → List Byte
  /-- The chosen byte-level MD padding/strengthening. -/
  padding : List Byte → List Byte
  /-- Convert a byte string, including native padding, to compression blocks. -/
  blockify : List Byte → List Block
  /-- Serializing the output blocks gives exactly the padded byte string. -/
  blockify_padding (message : List Byte) :
    (blockify message).flatMap encodeBlock = padding message
  /-- Every block emitted by `blockify` is a full compression block. -/
  blockify_full (message : List Byte) (block : Block) :
    block ∈ blockify message → (encodeBlock block).length = blockSize
  /-- The exact codec-faithfulness premise needed by the concrete C2SP
  realization.  Together with `encodeItems_injective`, this says that native
  padding and block serialization do not identify two encoded input
  sequences.  It is deliberately weaker than prefix-freeness: C2SP item
  encodings are not prefix-free, and the Gażi theorem discharges its own local
  prefix-free obligation by appending a fresh delimiter block. -/
  blockify_encodeItems_injective :
    Function.Injective (fun M : InputSequence => blockify (encodeItems M))

/-- Construction-facing spelling of the weakest codec faithfulness law used
by the concrete SequenceMAC realization. -/
theorem blockifyEncodeItems_injective {Block : Type*} (codec : MDCodec Block) :
    Function.Injective
      (fun M : InputSequence => codec.blockify (encodeItems M)) :=
  codec.blockify_encodeItems_injective

/-- MD iteration from an IV over a block list. `List.foldl`, not a bespoke
recursor. -/
def mdIterate {State Block : Type*}
    (f : Compression State Block) (iv : State) : List Block → State :=
  fun blocks => blocks.foldl f iv

/-- Iterating over appended block strings threads the intermediate chaining
value into the suffix.  This is exactly `List.foldl_append`. -/
theorem mdIterate_append {State Block : Type*}
    (f : Compression State Block) (iv : State) (xs ys : List Block) :
    mdIterate f iv (xs ++ ys) =
      mdIterate f (mdIterate f iv xs) ys := by
  exact List.foldl_append

/-- The Merkle–Damgård hash `MD[f]`: apply the codec's native padding and then
iterate the compression transition from the public IV. -/
def mdHash {State Block : Type*} (codec : MDCodec Block)
    (f : Compression State Block) (iv : State) : List Byte → State :=
  fun message => mdIterate f iv (codec.blockify message)

end SequenceHash
