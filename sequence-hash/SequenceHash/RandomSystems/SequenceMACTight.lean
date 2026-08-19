import SequenceHash.RandomSystems.SequenceMACIndiffMD

/-!
# Structural strong-multi-user SequenceMAC bound

This module records the standard-model R6 assembly.  Backendal's strong
multi-user NMAC reduction is proved in `MACPRF.nmac_prf_bound_strong_mu`;
only the SequenceFunction safe-schedule normalization remains an explicit
hypothesis of the headline theorem.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18

namespace SequenceHash

open RandomSystems RandomSystems.CR18

namespace RandomSystemsModel

/-- The existing sampled-key SequenceMAC law, viewed through the canonical
`SequenceFunction` model.  The equalities
`sequenceMAC_eq_sequenceFunction` and
`sequenceMACStep_eq_sequenceFunctionStep` certify the function and converter
schedule used by `SM_H`; no construction input or step is repeated here. -/
noncomputable def sequenceFunctionReal {B : Type*} {L : U128}
    (codec : MDCodec B) (iv : HashOutput L)
    (f : MACPRF.CompressionFamily (HashOutput L) B) (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey) :
    PFunPDS InputSequence (HashOutput L) :=
  SM_H b S DK (mdHashLaw codec iv f)

/-- A trace-facing depth certificate for the canonical SequenceFunction body.

The first conjunct is the Backendal/NMAC accounting identity used by R6.  The
second says that every query-producing point of the canonical
`sequenceFunctionStep` schedule fits the certified compression depth; it is a
property of the existing step, not a duplicate schedule. -/
def SequenceFunctionBodyDepth {B : Type*} (codec : MDCodec B)
    (b : BlockSize) (S : ByteString) (ℓ dBody : ℕ) : Prop :=
  dBody = ℓ + 2 ∧
    ∀ {L : U128} (K : SequenceMACKey) (M : InputSequence)
      (ys : List (HashOutput L)) (x : List Byte),
      sequenceFunctionStep b K.1 S fSeqMac M ys = Sum.inl x →
        (codec.blockify x).length ≤ dBody

/-- Explicit safe-schedule normalization facade for canonical
`SequenceFunction`.

The witness is the normalized NMAC core on the construction's outside
interface.  `schedule_le` is the safe canonical-schedule leg, with the raw
long-derive residual charged once.  `core_le_nmac` is the query-preserving
normalization/DPI bridge to the existing independent-key NMAC laws.  Proving
these two deep properties is the separate `R6.deep` task. -/
def SequenceFunctionSafeScheduleBound {B : Type*} {L : U128}
    [Fintype B] [Nonempty B] [DecidableEq B]
    (codec : MDCodec B) (iv : HashOutput L)
    (f : MACPRF.CompressionFamily (HashOutput L) B) (b : BlockSize)
    (S : ByteString) (DK : RandomSystems.Dist SequenceMACKey)
    (epsSchedule : ℝ) : Prop :=
  ∃ normalizedCore : PFunPDS InputSequence (HashOutput L),
    (∀ q : ℕ, DK.isProbDist → DeriveSafeS_SEQ b S DK →
      Δ(⌈q⌉ sequenceFunctionReal codec iv f b S DK,
          ⌈q⌉ normalizedCore) ≤
        epsSchedule +
          (if q = 0 then 0 else (DeriveCost_SEQ b S DK : ℝ))) ∧
    (∀ (q ℓ : ℕ) (pad : HashOutput L ↪ B),
      Δ(⌈q⌉ normalizedCore,
          ⌈q⌉ PFunPDS.URF
            (X := InputSequence) (Y := HashOutput L)) ≤
        Δ(⌈q⌉ MACPRF.nmacReal ℓ f pad,
          ⌈q⌉ MACPRF.macIdeal ℓ))

/-- R6 headline: one triangle through the normalized NMAC core.

The strong multi-user NMAC term is discharged by
`MACPRF.nmac_prf_bound_strong_mu`; `hSchedule` is the remaining explicit
canonical safe-schedule normalization.  Everything else is the pure CR18
triangle and scalar accounting. -/
theorem sequenceFunction_prf_bound_strong_mu {B : Type*} {L : U128}
    [Fintype B] [Nonempty B] [DecidableEq B]
    (q ℓ dBody : ℕ) (codec : MDCodec B) (iv : HashOutput L)
    (f : MACPRF.CompressionFamily (HashOutput L) B) (b : BlockSize)
    (pad : HashOutput L ↪ B) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey) (hDK : DK.isProbDist)
    (hSafeS : DeriveSafeS_SEQ b S DK)
    (hTrace : SequenceFunctionBodyDepth codec b S ℓ dBody)
    (epsSchedule : ℝ)
    (hSchedule : SequenceFunctionSafeScheduleBound
      codec iv f b S DK epsSchedule) :
    Δ(⌈q⌉ sequenceFunctionReal codec iv f b S DK,
        ⌈q⌉ PFunPDS.URF
          (X := InputSequence) (Y := HashOutput L)) ≤
      epsSchedule +
        (if q = 0 then 0 else (DeriveCost_SEQ b S DK : ℝ)) +
        (dBody : ℝ) * MACPRF.epsCompMU q q f +
        (pairCollisionUnionBound (HashOutput L) q : ℝ) := by
  rcases hSchedule with ⟨normalizedCore, hSchedule, hCore⟩
  have hTriangle := maxAdvantage_triangle
    (⌈q⌉ sequenceFunctionReal codec iv f b S DK)
    (⌈q⌉ normalizedCore)
    (⌈q⌉ PFunPDS.URF (X := InputSequence) (Y := HashOutput L))
  calc
    Δ(⌈q⌉ sequenceFunctionReal codec iv f b S DK,
        ⌈q⌉ PFunPDS.URF
          (X := InputSequence) (Y := HashOutput L))
        ≤ Δ(⌈q⌉ sequenceFunctionReal codec iv f b S DK,
              ⌈q⌉ normalizedCore) +
            Δ(⌈q⌉ normalizedCore,
              ⌈q⌉ PFunPDS.URF
                (X := InputSequence) (Y := HashOutput L)) := hTriangle
    _ ≤ (epsSchedule +
            (if q = 0 then 0 else (DeriveCost_SEQ b S DK : ℝ))) +
          Δ(⌈q⌉ MACPRF.nmacReal ℓ f pad,
            ⌈q⌉ MACPRF.macIdeal ℓ) :=
      add_le_add (hSchedule q hDK hSafeS) (hCore q ℓ pad)
    _ ≤ (epsSchedule +
            (if q = 0 then 0 else (DeriveCost_SEQ b S DK : ℝ))) +
          ((ℓ + 2 : ℝ) * MACPRF.epsCompMU q q f +
            (pairCollisionUnionBound (HashOutput L) q : ℝ)) := by
      gcongr
      exact MACPRF.nmac_prf_bound_strong_mu q ℓ f pad
    _ = epsSchedule +
          (if q = 0 then 0 else (DeriveCost_SEQ b S DK : ℝ)) +
          (dBody : ℝ) * MACPRF.epsCompMU q q f +
          (pairCollisionUnionBound (HashOutput L) q : ℝ) := by
      rw [hTrace.1]
      push_cast
      ring

end RandomSystemsModel

end SequenceHash
