/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SpoC.DDC

/-! SpoC-128 instantiated with the NIST submission's sLiSCP-light-256 permutation. -/

namespace RandomSystems.SpoC.NIST

open RandomSystems.CR18
open RandomSystems.HCTR2Final.Bits
open scoped RandomSystems.HCTR2Final.Bits

abbrev Byte := BitString 8
abbrev Half := BitString 32
abbrev Word := BitString 64
abbrev Words := (Word × Word) × (Word × Word)

def splitBits (a b : ℕ) : BitString (a + b) ≃ BitString a × BitString b where
  toFun x := (x[0; a], x[a; b])
  invFun x := x.1 ∥ x.2
  left_inv := RandomSystems.HCTR2Final.Bits.Facts.cat_sub_sub
  right_inv x := by
    simp [RandomSystems.HCTR2Final.Bits.Facts.sub_cat_left,
      RandomSystems.HCTR2Final.Bits.Facts.sub_cat_right]

def words : State ≃ Words :=
  (splitBits 128 128).trans
    (Equiv.prodCongr (splitBits 64 64) (splitBits 64 64))

def physicalLayout : Words ≃ Words where
  toFun x := ((x.2.1, x.1.1), (x.2.2, x.1.2))
  invFun x := ((x.1.2, x.2.2), (x.1.1, x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rotateLane (x : Half) (shift : ℕ) : Half :=
  let b0 : Byte := x[0; 8]
  let b1 : Byte := x[8; 8]
  let b2 : Byte := x[16; 8]
  let b3 : Byte := x[24; 8]
  ((b0 <<< shift) ||| (b1 >>> (8 - shift))) ∥
  ((b1 <<< shift) ||| (b2 >>> (8 - shift))) ∥
  ((b2 <<< shift) ||| (b3 >>> (8 - shift))) ∥
  ((b3 <<< shift) ||| (b0 >>> (8 - shift)))

def simeckFunction (x : Half) : Half :=
  rotateLane x 1 ^^^ (rotateLane x 5 &&& x)

def simeckConstant (roundConstant round : ℕ) : Half :=
  (0xff : Byte) ∥ (0xff : Byte) ∥ (0xff : Byte) ∥
    BitVec.ofNat 8 (0xfe + ((roundConstant >>> round) &&& 1))

def simeckRound (constant : Half) : Equiv.Perm (Half × Half) where
  toFun x := ((simeckFunction x.1 ^^^ x.2) ^^^ constant, x.1)
  invFun x := (x.2, (simeckFunction x.2 ^^^ x.1) ^^^ constant)
  left_inv x := by
    ext <;> simp [BitVec.xor_assoc]
  right_inv x := by
    ext <;> simp [BitVec.xor_assoc]

def simeckBox (roundConstant : ℕ) : Equiv.Perm Word :=
  (splitBits 32 32).trans <|
    ((List.range 8).foldl
      (fun permutation round =>
        permutation.trans (simeckRound (simeckConstant roundConstant round)))
      (Equiv.refl (Half × Half))).trans (splitBits 32 32).symm

def stepConstant (constant : ℕ) : Word :=
  BitVec.ofNat 64 ((2 ^ 56 - 1) + constant * 2 ^ 56)

def sliscpStep (sc1 sc2 rc1 rc2 : ℕ) : Equiv.Perm Words where
  toFun x :=
    let f1 := simeckBox rc1 x.1.2
    let f3 := simeckBox rc2 x.2.2
    ((f1, (x.2.1 ^^^ f3) ^^^ stepConstant sc2),
      (f3, (x.1.1 ^^^ f1) ^^^ stepConstant sc1))
  invFun x :=
    let x1 := (simeckBox rc1).symm x.1.1
    let x3 := (simeckBox rc2).symm x.2.1
    ((((x.2.2 ^^^ x.1.1) ^^^ stepConstant sc1), x1),
      (((x.1.2 ^^^ x.2.1) ^^^ stepConstant sc2), x3))
  left_inv x := by
    dsimp
    simp only [Equiv.symm_apply_apply]
    apply Prod.ext
    · apply Prod.ext
      · calc
          _ = (stepConstant sc1 ^^^ stepConstant sc1) ^^^
              (((simeckBox rc1) x.1.2 ^^^ (simeckBox rc1) x.1.2) ^^^ x.1.1) := by
                ac_rfl
          _ = x.1.1 := by simp
      · rfl
    · apply Prod.ext
      · calc
          _ = (stepConstant sc2 ^^^ stepConstant sc2) ^^^
              (((simeckBox rc2) x.2.2 ^^^ (simeckBox rc2) x.2.2) ^^^ x.2.1) := by
                ac_rfl
          _ = x.2.1 := by simp
      · rfl
  right_inv x := by
    dsimp
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · calc
          _ = (stepConstant sc2 ^^^ stepConstant sc2) ^^^
              ((x.2.1 ^^^ x.2.1) ^^^ x.1.2) := by ac_rfl
          _ = x.1.2 := by simp
    · apply Prod.ext
      · rfl
      · calc
          _ = (stepConstant sc1 ^^^ stepConstant sc1) ^^^
              ((x.1.1 ^^^ x.1.1) ^^^ x.2.2) := by ac_rfl
          _ = x.2.2 := by simp

def stepConstants1 : List ℕ :=
  [0x08, 0x86, 0xe2, 0x89, 0xe6, 0xca, 0x17, 0x8e, 0x64,
   0x6b, 0x6f, 0x2c, 0xdd, 0x99, 0xea, 0x0f, 0x04, 0x43]

def stepConstants2 : List ℕ :=
  [0x64, 0x6b, 0x6f, 0x2c, 0xdd, 0x99, 0xea, 0x0f, 0x04,
   0x43, 0xf1, 0x44, 0x73, 0xe5, 0x0b, 0x47, 0xb2, 0xb5]

def roundConstants1 : List ℕ :=
  [0x0f, 0x04, 0x43, 0xf1, 0x44, 0x73, 0xe5, 0x0b, 0x47,
   0xb2, 0xb5, 0x37, 0x96, 0xee, 0x4c, 0xf5, 0x07, 0x82]

def roundConstants2 : List ℕ :=
  [0x47, 0xb2, 0xb5, 0x37, 0x96, 0xee, 0x4c, 0xf5, 0x07,
   0x82, 0xa1, 0x78, 0xa2, 0xb9, 0xf2, 0x85, 0x23, 0xd9]

def physicalPermutation : Equiv.Perm Words :=
  (List.range 18).foldl
    (fun permutation round =>
      permutation.trans (sliscpStep
        (stepConstants1.getD round 0) (stepConstants2.getD round 0)
        (roundConstants1.getD round 0) (roundConstants2.getD round 0)))
    (Equiv.refl Words)

def permutation : Equiv.Perm State :=
  words |>.trans physicalLayout |>.trans physicalPermutation |>.trans
    physicalLayout.symm |>.trans words.symm

noncomputable def pds : PFunPDS.Prob Query Response :=
  spocPDS permutation

def katKey : Block := 0x0f0e0d0c0b0a09080706050403020100
def katNonce : Block := katKey
def katPlaintext : Block := katKey
def katCiphertext : Block := 0x79b1b6c1cd4597b96a2dd1b825ec4859
def katTag : Block := 0xed175848cb726faed8f3c1392f106692
def katQuery : Query := Sum.inl ⟨katNonce, [], [katPlaintext]⟩

def katPermutationAnswers : List State :=
  let plaintextOutput := permutation (load katKey katNonce)
  let afterPlaintext := (processData false katPlaintext plaintextOutput).1
  [plaintextOutput, permutation (tagInput afterPlaintext)]

set_option maxRecDepth 100000 in
/-- Count 529 from the NIST Round 2 SpoC-128 known-answer vectors. -/
theorem known_answer :
    spoc katKey katQuery katPermutationAnswers =
      Sum.inr (Sum.inl ⟨[katCiphertext], katTag⟩) := by
  rfl

end RandomSystems.SpoC.NIST
