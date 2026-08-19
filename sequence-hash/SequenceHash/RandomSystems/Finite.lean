import SequenceHash.Spec
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite carriers for SequenceHash security games

The pure C2SP model deliberately uses bounded list subtypes instead of an
implementation-sized approximation. Those types are finite, although their
cardinalities are far too large to enumerate computationally. The
RandomSystems probability laws only need the mathematical `Fintype`
instances supplied here.

Keeping these noncomputable instances out of `Encoding` and `Spec` preserves
the pure layer's small import surface.
-/

namespace SequenceHash

noncomputable section

/-- The specification-bounded byte-string carrier is finite. -/
instance instFintypeByteString : Fintype ByteString :=
  (List.finite_length_lt Byte u128Modulus).fintype

/-- The specification-bounded sequence carrier is finite. -/
instance instFintypeInputSequence : Fintype InputSequence :=
  (List.finite_length_lt ByteString u128Modulus).fintype

/-- There is always at least one bounded byte string (the empty string). -/
instance instNonemptyByteString : Nonempty ByteString :=
  ⟨⟨[], by simp [u128Modulus]⟩⟩

/-- There is always at least one bounded input sequence (the empty sequence). -/
instance instNonemptyInputSequence : Nonempty InputSequence :=
  ⟨⟨[], by simp [u128Modulus]⟩⟩

/-- Fixed-length digest lists are finite. -/
instance instFintypeHashOutput (L : U128) : Fintype (HashOutput L) :=
  (List.finite_length_eq Byte L.val).fintype

/-- A canonical all-zero digest, used as an irrelevant default when extending
a function from the finite set of call strings to all byte strings. -/
def zeroHashOutput (L : U128) : HashOutput L :=
  ⟨List.replicate L.val 0, by simp⟩

instance instNonemptyHashOutput (L : U128) : Nonempty (HashOutput L) :=
  ⟨zeroHashOutput L⟩

/-- A byte digest of length `L` has exactly `256 ^ L` possible values. -/
@[simp]
theorem card_hashOutput (L : U128) :
    Fintype.card (HashOutput L) = 256 ^ L.val := by
  let e : HashOutput L ≃ (Fin L.val → Byte) :=
    Equiv.vectorEquivFin Byte L.val
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- A byte digest of length `L` has exactly `2 ^ (8 * L)` possible values. -/
theorem card_hashOutput_eq_two_pow (L : U128) :
    Fintype.card (HashOutput L) = 2 ^ (8 * L.val) := by
  rw [card_hashOutput]
  calc
    256 ^ L.val = (2 ^ 8) ^ L.val := by norm_num
    _ = 2 ^ (8 * L.val) := by rw [pow_mul]

end

end SequenceHash
