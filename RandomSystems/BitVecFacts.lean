/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Card

/-!
# BitVec facts

`Fintype`/cardinality for `BitVec` (via mathlib's `BitVec.equivFin`) and zero-extension
(`setWidth`) algebra.  All mathlib-PR candidates; delete each on upstream arrival.
-/

namespace RandomSystems.CR18

/-- `Fintype (BitVec w)` via `BitVec.equivFin : BitVec w ≃+* Fin (2^w)`. -/
instance instFintypeBitVec (w : ℕ) : Fintype (BitVec w) :=
  Fintype.ofEquiv _ BitVec.equivFin.toEquiv.symm

/-- `|BitVec w| = 2^w`. -/
theorem card_bitVec (w : ℕ) : Fintype.card (BitVec w) = 2 ^ w := by
  rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin]

variable {n : ℕ}

/-- Zero-extension `BitVec r → BitVec n` is injective for `r ≤ n`. -/
theorem setWidth_injective {r : ℕ} (h : r ≤ n) :
    Function.Injective (BitVec.setWidth n : BitVec r → BitVec n) := by
  intro a b hab
  have hn := congrArg BitVec.toNat hab
  rw [BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h] at hn
  exact BitVec.toNat_inj.mp hn

/-- Zero-extension commutes with XOR (`r ≤ n`). -/
theorem setWidth_xor_of_le {r : ℕ} (h : r ≤ n) (a b : BitVec r) :
    (a ^^^ b).setWidth n = a.setWidth n ^^^ b.setWidth n := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth_of_le h, BitVec.toNat_xor, BitVec.toNat_xor,
    BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h]

/-- Zero-extension round-trips for `r ≤ n`. -/
theorem setWidth_setWidth_of_le {r : ℕ} (h : r ≤ n) (a : BitVec r) :
    (a.setWidth n).setWidth r = a := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le h, Nat.mod_eq_of_lt a.isLt]

end RandomSystems.CR18
