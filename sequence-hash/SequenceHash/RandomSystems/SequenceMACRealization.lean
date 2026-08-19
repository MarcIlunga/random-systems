import SequenceHash.RandomSystems.SequenceFunctionCore
import SequenceHash.RandomSystems.SequenceMACPRF

/-!
# Concrete C2SP SequenceMAC realization

This file is the statement-first bridge from the literal byte construction in
C2SP `sequencehash.md` to the proven block-level Gażi--Pietrzak--Rybár theorem
in `SequenceMACPRF.lean`.

The concrete system samples one C2SP-valid key, shares it across all outside
queries, and applies the keyed `F = 1` converter schedule to the fixed
Merkle--Damgård hash `MD[f]`.  The bridge term deliberately contains both the
domain-separated run-up replacement and the normalization of C2SP's framed,
possibly multi-block outer cascade to the one-call outer layer of NMAC.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18 RandomSystems.CR18.PFunConverter.DDC

namespace SequenceHash

open RandomSystems RandomSystems.CR18

namespace RandomSystemsModel

/-- The block size carried by an `MDCodec`, in the positive form expected by
the literal C2SP header and derivation functions. -/
def codecBlockSize {B : Type*} (codec : MDCodec B) : BlockSize :=
  ⟨codec.blockSize, codec.blockSize_pos⟩

/-- Exact C2SP SequenceMAC inner input after the derived key block has been
computed once. -/
def sequenceMACInnerInput (b : BlockSize) (K : SequenceMACKey)
    (derivedK : List Byte) (M : InputSequence) : List Byte :=
  headerI b fSeqMac K.1 ++ derivedK ++ encodeItems M

/-- Exact C2SP SequenceMAC outer input after the customization and key blocks
and the inner digest have been computed.  The item count and digest length are
fixed-width MSBF fields, exactly as in `SequenceFunction`. -/
def sequenceMACOuterInput {L : U128} (b : BlockSize) (S : ByteString)
    (K : SequenceMACKey) (M : InputSequence) (derivedS derivedK : List Byte)
    (inner : HashOutput L) : List Byte :=
  headerO b fSeqMac S K.1 ++ derivedS ++ derivedK ++
    encodeMSBF ⟨M.val.length, M.property⟩ ++ encodeMSBF L ++ inner.val

/-- Literal C2SP `SequenceMAC`, i.e. `SequenceFunction` with a nonempty
C2SP-valid key and `F = 1`.  Both `K'` and `S'` are derived once and reused. -/
def sequenceMAC {L : U128} (b : BlockSize) (H : FixedHash L)
    (S : ByteString) (K : SequenceMACKey) (M : InputSequence) : HashOutput L :=
  let derivedK := derive K.1.val H b
  let derivedS := derive S.val H b
  let inner := H (sequenceMACInnerInput b K derivedK M)
  H (sequenceMACOuterInput b S K M derivedS derivedK inner)

/-- One outside SequenceMAC query as a protocol over a fixed-output hash
resource.  Long-key and long-customization derivations are each queried once;
the final outer call receives C2SP's complete framed envelope. -/
def sequenceMACStep {L : U128} (b : BlockSize) (S : ByteString)
    (K : SequenceMACKey) (M : InputSequence)
    (ys : List (HashOutput L)) : List Byte ⊕ HashOutput L :=
  if K.1.val.length ≤ b.val then
    if S.val.length ≤ b.val then
      match ys with
      | [] =>
          Sum.inl (sequenceMACInnerInput b K (pad K.1.val b) M)
      | inner :: [] =>
          Sum.inl (sequenceMACOuterInput b S K M
            (pad S.val b) (pad K.1.val b) inner)
      | _ :: outer :: _ => Sum.inr outer
    else
      match ys with
      | [] => Sum.inl S.val
      | _derivedS :: [] =>
          Sum.inl (sequenceMACInnerInput b K (pad K.1.val b) M)
      | derivedS :: inner :: [] =>
          Sum.inl (sequenceMACOuterInput b S K M
            (pad derivedS.val b) (pad K.1.val b) inner)
      | _ :: _ :: outer :: _ => Sum.inr outer
  else
    if S.val.length ≤ b.val then
      match ys with
      | [] => Sum.inl K.1.val
      | derivedK :: [] =>
          Sum.inl (sequenceMACInnerInput b K (pad derivedK.val b) M)
      | derivedK :: inner :: [] =>
          Sum.inl (sequenceMACOuterInput b S K M
            (pad S.val b) (pad derivedK.val b) inner)
      | _ :: _ :: outer :: _ => Sum.inr outer
    else
      match ys with
      | [] => Sum.inl K.1.val
      | _derivedK :: [] => Sum.inl S.val
      | derivedK :: _derivedS :: [] =>
          Sum.inl (sequenceMACInnerInput b K (pad derivedK.val b) M)
      | derivedK :: derivedS :: inner :: [] =>
          Sum.inl (sequenceMACOuterInput b S K M
            (pad derivedS.val b) (pad derivedK.val b) inner)
      | _ :: _ :: _ :: outer :: _ => Sum.inr outer

/-- The sampled-key C2SP SequenceMAC converter law.  Sampling occurs once, so
the same key is shared by every query to the resulting system. -/
noncomputable def sequenceMACConverter {L : U128} (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey) :
    PFunPDC InputSequence (HashOutput L) (List Byte) (HashOutput L) :=
  Dist.fTransform
    (fun K => PFunConverter.DDC.ofStep (sequenceMACStep (L := L) b S K)) DK

/-- The law-level C2SP SequenceMAC system obtained by applying the keyed
converter schedule to a distribution over fixed-output hash functions. -/
noncomputable def sequenceMACSystem {L : U128} (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey)
    (D : RandomSystems.Dist (FixedHash L)) :
    PFunPDS InputSequence (HashOutput L) :=
  PFunPDC.apply (sequenceMACConverter (L := L) b S DK)
    (PFunPDS.ofFunDist D)

/-- Pointwise keyed realization underlying `sequenceMACSystem_realization`.
The four branches are exactly the C2SP short/long key crossed with the
short/long customization schedule. -/
theorem sequenceMAC_ofStep_functionEvaluator {L : U128} (b : BlockSize)
    (S : ByteString) (K : SequenceMACKey) (H : FixedHash L) :
    (PFunConverter.DDC.ofStep (sequenceMACStep b S K) ·ᶜ
        PFunDDS.functionEvaluator H) =
      PFunDDS.functionEvaluator (fun M => sequenceMAC b H S K M) := by
  let calls : InputSequence → List (List Byte) := fun M =>
    if K.1.val.length ≤ b.val then
      if S.val.length ≤ b.val then
        let inner := sequenceMACInnerInput b K (pad K.1.val b) M
        [inner, sequenceMACOuterInput b S K M
          (pad S.val b) (pad K.1.val b) (H inner)]
      else
        let inner := sequenceMACInnerInput b K (pad K.1.val b) M
        [S.val, inner, sequenceMACOuterInput b S K M
          (pad (H S.val).val b) (pad K.1.val b) (H inner)]
    else
      if S.val.length ≤ b.val then
        let inner := sequenceMACInnerInput b K (pad (H K.1.val).val b) M
        [K.1.val, inner, sequenceMACOuterInput b S K M
          (pad S.val b) (pad (H K.1.val).val b) (H inner)]
      else
        let inner := sequenceMACInnerInput b K (pad (H K.1.val).val b) M
        [K.1.val, S.val, inner, sequenceMACOuterInput b S K M
          (pad (H S.val).val b) (pad (H K.1.val).val b) (H inner)]
  let rounds : InputSequence → Nat := fun _ =>
    if K.1.val.length ≤ b.val then
      if S.val.length ≤ b.val then 2 else 3
    else if S.val.length ≤ b.val then 3 else 4
  have hrawTwo (xs : List (List Byte)) (x₁ x₂ : List Byte) :
      (PFunDDS.functionEvaluator H).1 (xs ++ [x₁, x₂]) =
        Part.some (H x₂) := by
    rw [show xs ++ [x₁, x₂] = (xs ++ [x₁]) ++ [x₂] by simp]
    exact CausalApply.functionEvaluator_raw_append H (xs ++ [x₁]) x₂
  have hrawThree (xs : List (List Byte)) (x₁ x₂ x₃ : List Byte) :
      (PFunDDS.functionEvaluator H).1 (xs ++ [x₁, x₂, x₃]) =
        Part.some (H x₃) := by
    rw [show xs ++ [x₁, x₂, x₃] = (xs ++ [x₁, x₂]) ++ [x₃] by simp]
    exact CausalApply.functionEvaluator_raw_append H (xs ++ [x₁, x₂]) x₃
  have hrawFour (xs : List (List Byte)) (x₁ x₂ x₃ x₄ : List Byte) :
      (PFunDDS.functionEvaluator H).1 (xs ++ [x₁, x₂, x₃, x₄]) =
        Part.some (H x₄) := by
    rw [show xs ++ [x₁, x₂, x₃, x₄] =
      (xs ++ [x₁, x₂, x₃]) ++ [x₄] by simp]
    exact CausalApply.functionEvaluator_raw_append H
      (xs ++ [x₁, x₂, x₃]) x₄
  apply PFunConverter.DDC.apply_ofStep_functionEvaluator_of_round
      (sequenceMACStep b S K) H (fun M => sequenceMAC b H S K M)
      calls rounds (Bmax := 4)
  · intro M
    dsimp only [rounds]
    split <;> split <;> omega
  · intro M n xs
    by_cases hK : K.1.val.length ≤ b.val
    · by_cases hS : S.val.length ≤ b.val
      · simp [rounds, calls, sequenceMACStep, hK, hS, sequenceMAC, derive,
          CausalApply.driveG, CausalApply.functionEvaluator_raw_append,
          hrawTwo]
      · simp [rounds, calls, sequenceMACStep, hK, hS, sequenceMAC, derive,
          CausalApply.driveG, CausalApply.functionEvaluator_raw_append,
          hrawTwo, hrawThree]
    · by_cases hS : S.val.length ≤ b.val
      · simp [rounds, calls, sequenceMACStep, hK, hS, sequenceMAC, derive,
          CausalApply.driveG, CausalApply.functionEvaluator_raw_append,
          hrawTwo, hrawThree]
      · simp [rounds, calls, sequenceMACStep, hK, hS, sequenceMAC, derive,
          CausalApply.driveG, CausalApply.functionEvaluator_raw_append,
          hrawTwo, hrawThree, hrawFour]

/-- **Keyed converter realization.** This is the `F = 1` analogue of
`sequenceHashSystem_realization`: the converter law is exactly the
distribution of literal C2SP SequenceMAC functions. -/
theorem sequenceMACSystem_realization {L : U128} (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey)
    (D : RandomSystems.Dist (FixedHash L)) :
    sequenceMACSystem b S DK D =
      PFunPDS.ofFunDist
        (Dist.fTransform
          (fun p : SequenceMACKey × FixedHash L =>
            fun M => sequenceMAC b p.2 S p.1 M)
          (Dist.prod DK D)) := by
  have hprod :
      Dist.prod
          (Dist.fTransform
            (fun K => PFunConverter.DDC.ofStep
              (sequenceMACStep (L := L) b S K)) DK)
          (Dist.fTransform PFunDDS.functionEvaluator D) =
        Dist.fTransform
          (fun p : SequenceMACKey × FixedHash L =>
            (PFunConverter.DDC.ofStep (sequenceMACStep b S p.1),
              PFunDDS.functionEvaluator p.2))
          (Dist.prod DK D) := by
    classical
    apply Finsupp.ext
    intro p
    rcases p with ⟨a, s⟩
    rw [Dist.prod_apply, Dist.fTransform_apply_eq_mass,
      Dist.fTransform_apply_eq_mass, Dist.fTransform_apply_eq_mass]
    rw [show (fun p : SequenceMACKey × FixedHash L =>
        (PFunConverter.DDC.ofStep (sequenceMACStep b S p.1),
          PFunDDS.functionEvaluator p.2) = (a, s)) =
        (fun p =>
          PFunConverter.DDC.ofStep (sequenceMACStep b S p.1) = a ∧
            PFunDDS.functionEvaluator p.2 = s) by
      funext p
      simp]
    exact (Dist.mass_prod_and DK D _ _).symm
  unfold sequenceMACSystem sequenceMACConverter PFunPDC.apply PFunPDS.ofFunDist
  rw [hprod, Dist.fTransform_comp]
  rw [Dist.fTransform_comp]
  apply congrArg
    (fun F : (SequenceMACKey × FixedHash L) →
        PFunDDS.DDS InputSequence (HashOutput L) =>
      Dist.fTransform F (Dist.prod DK D))
  funext p
  exact sequenceMAC_ofStep_functionEvaluator b S p.1 p.2

/-- The point law of the fixed Merkle--Damgård hash `MD[f]`. -/
noncomputable def mdHashLaw {B : Type*} {L : U128} (codec : MDCodec B)
    (iv : HashOutput L) (f : MACPRF.CompressionFamily (HashOutput L) B) :
    RandomSystems.Dist (FixedHash L) :=
  Finsupp.single (mdHash codec f iv) 1

/-- The concrete real world over `InputSequence`: the keyed C2SP `F = 1`
converter schedule applied to the fixed compression-family realization
`MD[f]`. -/
noncomputable def concreteSequenceMACReal {B : Type*} {L : U128}
    (codec : MDCodec B) (iv : HashOutput L)
    (f : MACPRF.CompressionFamily (HashOutput L) B) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey) :
    PFunPDS InputSequence (HashOutput L) :=
  sequenceMACSystem (codecBlockSize codec) S DK (mdHashLaw codec iv f)

/-- The bounded injective translation used to pull the block-level theorem
back to literal input sequences.  Only the aligned inner suffix is translated:
the domain-separated `HeaderI || K'` run-up remains inside `epsC2SP`. -/
def inputSequenceBlockEmbedding {B : Type*} (codec : MDCodec B) (ℓ : ℕ)
    (hℓ : ∀ M : InputSequence,
      (codec.blockify (encodeItems M)).length ≤ ℓ) :
    InputSequence ↪ MACPRF.BlockString B ℓ where
  toFun M := ⟨codec.blockify (encodeItems M), hℓ M⟩
  inj' := by
    intro M N h
    apply blockifyEncodeItems_injective codec
    exact congrArg Subtype.val h

/-- Pull a block-level system back along the one-query input translation.
The converter makes exactly one block-system query per outside query. -/
noncomputable def pullbackBlockSystem {B C : Type*} {ℓ : ℕ}
    (e : InputSequence ↪ MACPRF.BlockString B ℓ)
    (P : PFunPDS (MACPRF.BlockString B ℓ) C) :
    PFunPDS InputSequence C :=
  PFunPDS.applyDDC
    (PFunConverter.DDC.simple e (id : C → C)) P

/-- Pulling a uniform random function back along an injective input
translation is again a uniform random function. -/
theorem pullbackBlockSystem_URF {B C : Type*} {ℓ : ℕ}
    [Fintype B] [Nonempty B] [DecidableEq B]
    [Fintype C] [Nonempty C] [DecidableEq C]
    (e : InputSequence ↪ MACPRF.BlockString B ℓ) :
    pullbackBlockSystem e
        (PFunPDS.URF (X := MACPRF.BlockString B ℓ) (Y := C)) =
      PFunPDS.URF (X := InputSequence) (Y := C) := by
  unfold pullbackBlockSystem PFunPDS.URF
  rw [PFunPDS.applyDDC_simple_ofFunDist]
  congr 1
  simpa using
    (MACPRF.gazi_uniform_restrict
      (I := InputSequence) (J := MACPRF.BlockString B ℓ) (A := C) e)

/-- The independent-uniform block-level SequenceMAC/NMAC world, restricted
to C2SP input sequences through the bounded injective block translation. -/
noncomputable def blockSequenceMACReal {B : Type*} {L : U128}
    [Fintype B] [Nonempty B] [DecidableEq B]
    [DecidableEq (HashOutput L)]
    (ℓ : ℕ) (codec : MDCodec B)
    (f : MACPRF.CompressionFamily (HashOutput L) B)
    (padC : HashOutput L ↪ B)
    (hℓ : ∀ M : InputSequence,
      (codec.blockify (encodeItems M)).length ≤ ℓ) :
    PFunPDS InputSequence (HashOutput L) :=
  pullbackBlockSystem (inputSequenceBlockEmbedding codec ℓ hℓ)
    (MACPRF.nmacReal ℓ f padC)

/-- The exact C2SP realization bridge.  It contains both the concrete
domain-separated run-ups (including long-key/long-customization derivations)
and normalization of the framed multi-block outer cascade to Gażi NMAC's
single outer compression call.  No definitional NMAC equality is claimed. -/
noncomputable def epsC2SP {B : Type*} {L : U128}
    [Fintype B] [Nonempty B] [DecidableEq B]
    [DecidableEq (HashOutput L)]
    (q ℓ : ℕ) (codec : MDCodec B) (iv : HashOutput L)
    (f : MACPRF.CompressionFamily (HashOutput L) B)
    (padC : HashOutput L ↪ B) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (hℓ : ∀ M : InputSequence,
      (codec.blockify (encodeItems M)).length ≤ ℓ) : ℝ :=
  Δ(⌈q⌉ concreteSequenceMACReal codec iv f S DK,
    ⌈q⌉ blockSequenceMACReal ℓ codec f padC hℓ)

/-- **GUARDRAIL: concrete C2SP SequenceMAC (`F = 1`) over
`InputSequence`.**  This statement connects the literal converter realization
to the proven block-level theorem.  Its only construction-specific loss is the
explicit `epsC2SP` distance. -/
theorem sequenceMAC_prf_bound_concrete {B : Type*} {L : U128}
    [Fintype B] [Nonempty B] [DecidableEq B]
    [DecidableEq (HashOutput L)]
    (q ℓ : ℕ) (codec : MDCodec B) (iv : HashOutput L)
    (f : MACPRF.CompressionFamily (HashOutput L) B)
    (padC : HashOutput L ↪ B) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (hℓ : ∀ M : InputSequence,
      (codec.blockify (encodeItems M)).length ≤ ℓ)
    (εna : NNReal) (hna : MACPRF.CompNASecure q f εna) :
    Δ(⌈q⌉ concreteSequenceMACReal codec iv f S DK,
        ⌈q⌉ PFunPDS.URF
          (X := InputSequence) (Y := HashOutput L))
      ≤ epsC2SP q ℓ codec iv f padC S DK hℓ
        + Δ(⌈q⌉ MACPRF.compReal f, ⌈q⌉ MACPRF.compIdeal)
        + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
        + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card (HashOutput L) : ℝ) := by
  let e := inputSequenceBlockEmbedding codec ℓ hℓ
  have hone : PFunConverter.DDC.AnswersWithin
      (PFunConverter.DDC.simpleStep e (id : HashOutput L → HashOutput L)) 1 := by
    intro M ys hys
    cases ys with
    | nil => simp at hys
    | cons y ys => exact ⟨y, rfl⟩
  have hnmacRF : PFunPDS.IsRandomFunction (MACPRF.nmacReal ℓ f padC) := by
    unfold MACPRF.nmacReal MACPRF.sequenceMACReal
    exact PFunPDS.ofFunDist_isRandomFunction _
  have hidealRF : PFunPDS.IsRandomFunction
      (MACPRF.macIdeal (B := B) (C := HashOutput L) ℓ) := by
    unfold MACPRF.macIdeal
    exact PFunPDS.URF_isRandomFunction
      (X := MACPRF.BlockString B ℓ) (Y := HashOutput L)
  have hpull :
      Δ(⌈q⌉ blockSequenceMACReal ℓ codec f padC hℓ,
          ⌈q⌉ PFunPDS.URF
            (X := InputSequence) (Y := HashOutput L))
        ≤ Δ(⌈q⌉ MACPRF.nmacReal ℓ f padC,
            ⌈q⌉ MACPRF.macIdeal ℓ) := by
    rw [show blockSequenceMACReal ℓ codec f padC hℓ =
        pullbackBlockSystem e (MACPRF.nmacReal ℓ f padC) from rfl,
      ← pullbackBlockSystem_URF e]
    simpa [pullbackBlockSystem, Nat.mul_one] using
      (maxAdvantage_filterQueries_applyDDC_le
        (PFunConverter.DDC.simpleStep e
          (id : HashOutput L → HashOutput L)) hone q
        (MACPRF.nmacReal ℓ f padC) (MACPRF.macIdeal ℓ)
        hnmacRF hidealRF)
  have hnmac := MACPRF.nmac_prf_bound q ℓ f padC εna hna
  calc
    Δ(⌈q⌉ concreteSequenceMACReal codec iv f S DK,
        ⌈q⌉ PFunPDS.URF
          (X := InputSequence) (Y := HashOutput L))
      ≤ Δ(⌈q⌉ concreteSequenceMACReal codec iv f S DK,
          ⌈q⌉ blockSequenceMACReal ℓ codec f padC hℓ) +
        Δ(⌈q⌉ blockSequenceMACReal ℓ codec f padC hℓ,
          ⌈q⌉ PFunPDS.URF
            (X := InputSequence) (Y := HashOutput L)) :=
        maxAdvantage_triangle _ _ _
    _ ≤ epsC2SP q ℓ codec iv f padC S DK hℓ +
        Δ(⌈q⌉ MACPRF.nmacReal ℓ f padC,
          ⌈q⌉ MACPRF.macIdeal ℓ) :=
      add_le_add (le_of_eq rfl) hpull
    _ ≤ epsC2SP q ℓ codec iv f padC S DK hℓ +
        (MACPRF.epsComp q f +
          (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ) +
          ((q ^ 2 : ℕ) : ℝ) /
            (Fintype.card (HashOutput L) : ℝ)) :=
      add_le_add (le_refl _) hnmac
    _ = epsC2SP q ℓ codec iv f padC S DK hℓ
        + Δ(⌈q⌉ MACPRF.compReal f, ⌈q⌉ MACPRF.compIdeal)
        + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
        + ((q ^ 2 : ℕ) : ℝ) /
          (Fintype.card (HashOutput L) : ℝ) := by
      unfold MACPRF.epsComp
      ring

end RandomSystemsModel

end SequenceHash
