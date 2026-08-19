import SequenceHash.SoundEncoding
import SequenceHash.RandomSystems.SequenceMACRealization
import RandomSystems.SwitchingLemma

/-!
# SequenceMAC PRF security from hash indifferentiability

This file freezes the R3 statement on the pure CR18 surface.  The real system
is the existing C2SP `F = 1` SequenceMAC converter applied to a law of hash
functions.  The ideal is the role-separated random-oracle schedule delivered
by hash indifferentiability, followed by the pure CR18 birthday encoding leg.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18

namespace SequenceHash

open RandomSystems RandomSystems.CR18

namespace RandomSystemsModel

/-! ## The finite active hash-call domain -/

/-- Extract the scheduled hash call, if the protocol has not yet returned its
outside answer. -/
def sequenceMACScheduledCall {L : U128} (b : BlockSize) (S : ByteString)
    (w : SequenceMACCallWitness L) : Option (List Byte) :=
  match sequenceMACStep b S w.1 w.2.1 w.2.2.1 with
  | Sum.inl x => some x
  | Sum.inr _ => none

/-- Exactly the byte strings queried in one of the four branches of the
existing SequenceMAC protocol step, over every key, message, and answer
history of length at most three.  This includes raw long-key/customization
derivation calls as well as framed inner and outer calls. -/
def sequenceMACActiveCallSet {L : U128} (b : BlockSize) (S : ByteString) :
    Set (List Byte) :=
  {x | some x ∈ Set.range (sequenceMACScheduledCall (L := L) b S)}

/-- Every query emitted by `sequenceMACStep` is in the active domain, directly
from its finite witness. -/
theorem sequenceMACScheduledCall_mem {L : U128} (b : BlockSize)
    (S : ByteString) (w : SequenceMACCallWitness L) (x : List Byte)
    (h : sequenceMACScheduledCall b S w = some x) :
    x ∈ sequenceMACActiveCallSet (L := L) b S := by
  exact ⟨w, h⟩

theorem sequenceMACActiveCallSet_finite {L : U128} (b : BlockSize)
    (S : ByteString) : (sequenceMACActiveCallSet (L := L) b S).Finite := by
  change (Function.Embedding.some ⁻¹'
    Set.range (sequenceMACScheduledCall (L := L) b S)).Finite
  exact Set.Finite.preimage_embedding Function.Embedding.some
    (Set.finite_range (sequenceMACScheduledCall (L := L) b S))

/-- The finite domain on which the SequenceMAC random oracle is sampled. -/
abbrev SequenceMACActiveCall {L : U128} (b : BlockSize) (S : ByteString) :=
  {x : List Byte // x ∈ sequenceMACActiveCallSet (L := L) b S}

noncomputable instance instFintypeSequenceMACActiveCall {L : U128}
    (b : BlockSize) (S : ByteString) :
    Fintype (SequenceMACActiveCall (L := L) b S) :=
  (sequenceMACActiveCallSet_finite (L := L) b S).fintype

/-- The R3 real system `SM_H`: the already-realized C2SP SequenceMAC converter
over the supplied law `D_H` of fixed-output hash functions. -/
noncomputable def SM_H {L : U128} (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (D_H : RandomSystems.Dist (FixedHash L)) :
    PFunPDS InputSequence (HashOutput L) :=
  sequenceMACSystem b S DK D_H

/-! ## The role-separated RO schedule

The two raw answers and the inner function are sampled independently; the
outer function is the independent URF supplied by `seededHashThenURFGame`.
This is the faithful ideal delivered by hash indifferentiability. -/

/-- The finite seed from which the separated SequenceMAC schedule computes
its outer RO input: one shared key, two role-separated derivation answers, and
an independent uniform inner-tag function. -/
abbrev SequenceMACSeparatedSeed (L : U128) :=
  SequenceMACKey ×
    (HashOutput L × (HashOutput L × (InputSequence → HashOutput L)))

/-- Independent law of the separated key/raw/inner seed. -/
noncomputable def sequenceMACSeparatedSeedDist {L : U128}
    (DK : RandomSystems.Dist SequenceMACKey) :
    RandomSystems.Dist (SequenceMACSeparatedSeed L) :=
  RandomSystems.Dist.prod DK
    (RandomSystems.Dist.prod (RandomSystems.Dist.uniform (HashOutput L))
      (RandomSystems.Dist.prod (RandomSystems.Dist.uniform (HashOutput L))
        (RandomSystems.Dist.uniform (InputSequence → HashOutput L))))

/-- The key block used by the separated schedule. -/
def sequenceMACSeparatedDerivedK {L : U128} (b : BlockSize)
    (a : SequenceMACSeparatedSeed L) : List Byte :=
  if a.1.1.val.length ≤ b.val then pad a.1.1.val b else pad a.2.1.val b

/-- The customization block used by the separated schedule. -/
def sequenceMACSeparatedDerivedS {L : U128} (b : BlockSize)
    (S : ByteString) (a : SequenceMACSeparatedSeed L) : List Byte :=
  if S.val.length ≤ b.val then pad S.val b else pad a.2.2.1.val b

/-- The `F = 1` framed inner encoding is injective in the outside input
sequence.  This is the keyed SequenceMAC form of R1's encoding-unambiguity
step and directly reuses `encodeItems_injective`. -/
theorem sequenceMACInnerInput_injective (b : BlockSize) (K : SequenceMACKey)
    (derivedK : List Byte) :
    Function.Injective (sequenceMACInnerInput b K derivedK) := by
  intro M N h
  apply encodeItems_injective
  simpa only [sequenceMACInnerInput, List.append_assoc] using
    List.append_cancel_left h

/-- The final framed outer call emitted by the role-separated schedule. -/
def sequenceMACSeparatedOuterCall {L : U128} (b : BlockSize) (S : ByteString)
    (a : SequenceMACSeparatedSeed L) (M : InputSequence) :
    SequenceMACActiveCall (L := L) b S := by
  let derivedK := sequenceMACSeparatedDerivedK b a
  let derivedS := sequenceMACSeparatedDerivedS b S a
  let inner := a.2.2.2 M
  refine ⟨sequenceMACOuterInput b S a.1 M derivedS derivedK inner, ?_⟩
  apply sequenceMACScheduledCall_mem b S
    (a.1, M, ⟨if a.1.1.val.length ≤ b.val then
      if S.val.length ≤ b.val then [inner]
      else [a.2.2.1, inner]
    else if S.val.length ≤ b.val then [a.2.1, inner]
      else [a.2.1, a.2.2.1, inner], by split <;> split <;> simp⟩)
  dsimp only [sequenceMACScheduledCall]
  by_cases hK : a.1.1.val.length ≤ b.val <;>
    by_cases hS : S.val.length ≤ b.val <;>
    simp [sequenceMACStep, sequenceMACSeparatedDerivedK,
      sequenceMACSeparatedDerivedS, hK, hS, derivedK, derivedS, inner]

/-- Equality of two separated outer calls at distinct outside inputs is an
actual collision of their distinct framed inner inputs.  This is the
SequenceMAC counterpart of R1's
`sequenceHash_collision_of_distinct_inputs`, specialized to the fixed key and
customization used by one MAC system. -/
theorem sequenceMACSeparatedOuterCall_collision {L : U128}
    (b : BlockSize) (S : ByteString) (a : SequenceMACSeparatedSeed L)
    {M N : InputSequence} (hMN : M ≠ N)
    (hOuter : sequenceMACSeparatedOuterCall b S a M =
      sequenceMACSeparatedOuterCall b S a N) :
    sequenceMACInnerInput b a.1 (sequenceMACSeparatedDerivedK b a) M ≠
        sequenceMACInnerInput b a.1 (sequenceMACSeparatedDerivedK b a) N ∧
      a.2.2.2 M = a.2.2.2 N := by
  constructor
  · exact fun h => hMN (sequenceMACInnerInput_injective b a.1 _ h)
  · have h := congrArg Subtype.val hOuter
    simp only [sequenceMACSeparatedOuterCall, sequenceMACOuterInput,
      List.append_assoc] at h
    have h := List.append_cancel_left h
    have h := List.append_cancel_left h
    have h := List.append_cancel_left h
    have hCode :
        encodeMSBF ⟨M.val.length, M.property⟩ =
          encodeMSBF ⟨N.val.length, N.property⟩ :=
      List.append_inj_left h (by simp)
    rw [hCode] at h
    have h := List.append_cancel_left h
    have h := List.append_cancel_left h
    exact Subtype.ext h

/-- The role-separated SequenceMAC world, definitionally in the form expected
by the shared condition-C endpoint. -/
noncomputable def SM_RO_separated {L : U128} (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey) :
    PFunPDS InputSequence (HashOutput L) :=
  PFunPDS.ignoreMBO
    (seededHashThenURFGame (O := HashOutput L)
      (sequenceMACSeparatedSeedDist DK)
      (sequenceMACSeparatedOuterCall (L := L) b S))

/-- A normalized key law and the three independent uniform role laws induce a
normalized separated seed. -/
theorem sequenceMACSeparatedSeedDist_isProbDist {L : U128}
    (DK : RandomSystems.Dist SequenceMACKey) (hDK : DK.isProbDist) :
    (sequenceMACSeparatedSeedDist (L := L) DK).isProbDist := by
  unfold sequenceMACSeparatedSeedDist
  exact RandomSystems.Dist.prod_isProbDist _ _ hDK
    (RandomSystems.Dist.prod_isProbDist _ _ RandomSystems.Dist.uniform_isProbDist
      (RandomSystems.Dist.prod_isProbDist _ _
        RandomSystems.Dist.uniform_isProbDist RandomSystems.Dist.uniform_isProbDist))

/-- A collision of the separated outer-input map forces a collision of the
uniform inner-tag function on two distinct outside inputs. -/
theorem sequenceMACSeparatedOuterCollision_imp_innerTagCollision {L : U128}
    (b : BlockSize) (S : ByteString) (a : SequenceMACSeparatedSeed L)
    (l : List InputSequence)
    (h : seededHashCollision
      (sequenceMACSeparatedOuterCall (L := L) b S) a l) :
    seededHashCollision (fun f : InputSequence → HashOutput L => f)
      a.2.2.2 l := by
  obtain ⟨M, hM, N, hN, hMN, hOuter⟩ := h
  exact ⟨M, hM, N, hN, hMN,
    (sequenceMACSeparatedOuterCall_collision b S a hMN hOuter).2⟩

/-- Per-blind-schedule collision leaf for the separated SequenceMAC seed.
The proof marginalizes the key and the two raw-role answers, then reuses the
existing fixed-query uniform-function birthday bound. -/
theorem sequenceMACSeparatedSeed_collision_mass_le {L : U128}
    (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey) (hDK : DK.isProbDist)
    (q : ℕ) (w : PFunDDS.Winner InputSequence (HashOutput L)) :
    (sequenceMACSeparatedSeedDist (L := L) DK).mass (fun a =>
      seededHashCollision (sequenceMACSeparatedOuterCall b S) a
        (blindQueryList w q)) ≤
      pairCollisionUnionBound (HashOutput L) q := by
  classical
  let l := blindQueryList w q
  let M₀ : InputSequence := Classical.choice inferInstance
  let xs : Fin q → InputSequence := fun i => l.getD i.1 M₀
  have hquery (M : InputSequence) (hM : M ∈ l) : ∃ i : Fin q, xs i = M := by
    have hi : l.idxOf M < q :=
      lt_of_lt_of_le (List.idxOf_lt_length_of_mem hM)
        (blindQueryList_length_le w q)
    refine ⟨⟨l.idxOf M, hi⟩, ?_⟩
    unfold xs
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hM)]
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hM)
  have hinner :
      (RandomSystems.Dist.uniform (InputSequence → HashOutput L)).mass
          (fun f => seededHashCollision
            (fun g : InputSequence → HashOutput L => g) f l) ≤
        pairCollisionUnionBound (HashOutput L) q := by
    refine (mass_mono _ fun f hf => ?_).trans
      (MACPRF.uniform_fixedQuery_collision_le (C := HashOutput L) q xs)
    obtain ⟨M, hM, N, hN, hMN, htag⟩ := hf
    obtain ⟨i, hi⟩ := hquery M hM
    obtain ⟨j, hj⟩ := hquery N hN
    exact ⟨i, j, fun hij => hMN (hi.symm.trans (hij ▸ hj)),
      fun hij => hMN (hi.symm.trans (hij.trans hj)), by simpa [hi, hj] using htag⟩
  calc
    (sequenceMACSeparatedSeedDist (L := L) DK).mass (fun a =>
        seededHashCollision (sequenceMACSeparatedOuterCall b S) a l) ≤
        (sequenceMACSeparatedSeedDist (L := L) DK).mass (fun a =>
          seededHashCollision (fun f : InputSequence → HashOutput L => f)
            a.2.2.2 l) :=
      mass_mono _ fun a =>
        sequenceMACSeparatedOuterCollision_imp_innerTagCollision b S a l
    _ = (RandomSystems.Dist.uniform (InputSequence → HashOutput L)).mass
          (fun f => seededHashCollision
            (fun g : InputSequence → HashOutput L => g) f l) := by
      unfold sequenceMACSeparatedSeedDist
      let Bad : (InputSequence → HashOutput L) → Prop := fun f =>
        seededHashCollision (fun g : InputSequence → HashOutput L => g) f l
      let U := RandomSystems.Dist.uniform (HashOutput L)
      let V := RandomSystems.Dist.uniform (InputSequence → HashOutput L)
      let Q₂ := RandomSystems.Dist.prod U V
      let Q₁ := RandomSystems.Dist.prod U Q₂
      change (RandomSystems.Dist.prod DK Q₁).mass
          (fun a => Bad a.2.2.2) = V.mass Bad
      calc
        _ = DK.weight * Q₁.mass (fun a => Bad a.2.2) :=
          RandomSystems.Dist.mass_prod_snd DK Q₁ (fun a => Bad a.2.2)
        _ = Q₁.mass (fun a => Bad a.2.2) := by rw [hDK, one_mul]
        _ = U.weight * Q₂.mass (fun a => Bad a.2) :=
          RandomSystems.Dist.mass_prod_snd U Q₂ (fun a => Bad a.2)
        _ = Q₂.mass (fun a => Bad a.2) := by
          rw [show U.weight = 1 from RandomSystems.Dist.uniform_isProbDist,
            one_mul]
        _ = U.weight * V.mass Bad :=
          RandomSystems.Dist.mass_prod_snd U V Bad
        _ = V.mass Bad := by
          rw [show U.weight = 1 from RandomSystems.Dist.uniform_isProbDist,
            one_mul]
    _ ≤ pairCollisionUnionBound (HashOutput L) q := hinner

/-! ## The encoding-collision term -/

/-- The role-separated ideal is within the standard inner-tag birthday term
of the VIL URF.  The adaptive collision step is the shared
`maxAdvantage_filterQueries_seededHashThenURF_le` endpoint. -/
theorem sequenceMAC_separated_encoding_bound {L : U128} (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey)
    (hDK : DK.isProbDist) (q : ℕ) :
    Δ(⌈q⌉ SM_RO_separated b S DK,
        ⌈q⌉ PFunPDS.URF (X := InputSequence) (Y := HashOutput L))
      ≤ (pairCollisionUnionBound (HashOutput L) q : ℝ) := by
  have hsep := maxAdvantage_filterQueries_seededHashThenURF_le
    (O := HashOutput L) (sequenceMACSeparatedSeedDist (L := L) DK)
    (sequenceMACSeparatedOuterCall (L := L) b S) q
    (pairCollisionUnionBound (HashOutput L) q)
    (sequenceMACSeparatedSeedDist_isProbDist DK hDK)
    (fun w _ => sequenceMACSeparatedSeed_collision_mass_le b S DK hDK q w)
  change
    Δ(⌈q⌉ SM_RO_separated (L := L) b S DK,
      ⌈q⌉ PFunPDS.URF
        (X := InputSequence) (Y := HashOutput L)) ≤
      (pairCollisionUnionBound (HashOutput L) q : ℝ) at hsep
  exact hsep

/-! ## R3 guardrail -/

/-- **GUARDRAIL (R3): SequenceMAC PRF security from hash
indifferentiability.**  The hash-indifferentiability leg targets the faithful
role-separated ideal; the encoding leg is the pure birthday bound above. -/
theorem sequenceMAC_prf_bound_indiff {L : U128} (q : ℕ) (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey)
    (D_H : RandomSystems.Dist (FixedHash L)) (ε_ind : ℕ → NNReal)
    (hDK : DK.isProbDist)
    (h_indiff : Δ(⌈q⌉ SM_H b S DK D_H, ⌈q⌉ SM_RO_separated b S DK)
      ≤ (ε_ind (4 * q) : ℝ)) :
    Δ(⌈q⌉ SM_H b S DK D_H,
        ⌈q⌉ PFunPDS.URF (X := InputSequence) (Y := HashOutput L))
      ≤ (ε_ind (4 * q) : ℝ) + (pairCollisionUnionBound (HashOutput L) q : ℝ) := by
  apply le_trans (maxAdvantage_triangle _ (⌈q⌉ SM_RO_separated b S DK) _)
  exact add_le_add h_indiff (sequenceMAC_separated_encoding_bound b S DK hDK q)

end RandomSystemsModel

end SequenceHash
