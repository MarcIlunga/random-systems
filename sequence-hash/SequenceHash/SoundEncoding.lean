import SequenceHash.Spec

/-!
# SequenceHash sound encoding (deterministic core of R1)

The deterministic soundness statement: when the underlying fixed-output hash `H`
is collision-free (injective), `SequenceHash` is injective on distinct
customization/sequence pairs. Equivalently, the C2SP encoding introduces no
collisions of its own — every `SequenceHash` collision is an actual `H`
collision. This is the collision-resistance half of the random-oracle soundness
(R1) and the fact the indifferentiability argument (R5) will consume.

The proof reuses the pure collision theorem
`sequenceHash_collision_of_distinct_inputs` directly: each of its three
collision disjuncts contradicts injectivity of `H`.
-/

namespace SequenceHash

/-- **Sound encoding (deterministic).** A collision-free `H` makes `SequenceHash`
injective on `(customization, item-sequence)` pairs. -/
theorem sequenceHash_pair_injective {L : U128} (b : BlockSize)
    (H : FixedHash L) (hH : Function.Injective H) :
    Function.Injective
      (fun p : ByteString × InputSequence => sequenceHash b H p.1 p.2) := by
  intro p q hOutput
  by_contra hInput
  rcases sequenceHash_collision_of_distinct_inputs b H hInput hOutput with
    hOuter | hInner | ⟨_, _, hDerive⟩
  · exact hOuter.1 (hH hOuter.2)
  · exact hInner.1 (hH hInner.2)
  · exact hDerive.1 (hH hDerive.2)

end SequenceHash
