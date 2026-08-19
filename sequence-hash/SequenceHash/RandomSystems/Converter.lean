import SequenceHash.Spec
import RandomSystems.ResourceView

/-!
# SequenceHash as a random system

The C2SP construction is presented as one outer-memoryless converter step,
then immediately as a law-level system. The realization theorem is the only
reason to introduce a call schedule or round bound, so both remain local to
that proof.
-/

namespace SequenceHash

open RandomSystems

namespace RandomSystemsModel

open RandomSystems.CR18

/-- One outside query to SequenceHash. -/
abbrev Query := ByteString × InputSequence

/-- SequenceHash as an outer-memoryless protocol over the hash resource. -/
def sequenceHashStep {L : U128} (b : BlockSize) (q : Query)
    (ys : List (HashOutput L)) : List Byte ⊕ HashOutput L :=
  if q.1.val.length ≤ b.val then
    match ys with
    | [] => Sum.inl (sequenceHashInnerInput b q.2)
    | inner :: [] =>
        Sum.inl
          (sequenceHashOuterInput b q.1 q.2 (pad q.1.val b) inner)
    | _ :: outer :: _ => Sum.inr outer
  else
    match ys with
    | [] => Sum.inl q.1.val
    | _derived :: [] => Sum.inl (sequenceHashInnerInput b q.2)
    | derived :: inner :: [] =>
        Sum.inl
          (sequenceHashOuterInput b q.1 q.2 (pad derived.val b) inner)
    | _ :: _ :: outer :: _ => Sum.inr outer

/-- The law-level SequenceHash system obtained by applying its converter to a
distribution over fixed-output hash functions. -/
noncomputable def sequenceHashSystem {L : U128} (b : BlockSize)
    (D : RandomSystems.Dist (FixedHash L)) :
    PFunPDS Query (HashOutput L) :=
  PFunPDS.applyDDC
    (PFunConverter.DDC.ofStep (sequenceHashStep (L := L) b))
    (PFunPDS.ofFunDist D)

/-- **Converter realization.** Applying the converter realizes the pure C2SP
SequenceHash construction as an equality of random-system laws. -/
theorem sequenceHashSystem_realization {L : U128} (b : BlockSize)
    (D : RandomSystems.Dist (FixedHash L)) :
    sequenceHashSystem b D =
      PFunPDS.ofFunDist
        (RandomSystems.Dist.fTransform
          (fun H q => sequenceHash b H q.1 q.2) D) := by
  unfold sequenceHashSystem
  apply PFunPDS.applyDDC_ofFunDist
  intro H
  let calls : Query → List (List Byte) := fun q =>
    let inner := sequenceHashInnerInput b q.2
    if q.1.val.length ≤ b.val then
      [inner,
        sequenceHashOuterInput b q.1 q.2 (pad q.1.val b) (H inner)]
    else
      [q.1.val, inner,
        sequenceHashOuterInput b q.1 q.2
          (pad (H q.1.val).val b) (H inner)]
  let B : Query → Nat := fun q =>
    if q.1.val.length ≤ b.val then 2 else 3
  have hrawTwo (xs : List (List Byte)) (x₁ x₂ : List Byte) :
      (PFunDDS.functionEvaluator H).1 (xs ++ [x₁, x₂]) =
        Part.some (H x₂) := by
    rw [show xs ++ [x₁, x₂] = (xs ++ [x₁]) ++ [x₂] by simp]
    exact CausalApply.functionEvaluator_raw_append H (xs ++ [x₁]) x₂
  have hrawThree (xs : List (List Byte)) (x₁ x₂ x₃ : List Byte) :
      (PFunDDS.functionEvaluator H).1 (xs ++ [x₁, x₂, x₃]) =
        Part.some (H x₃) := by
    rw [show xs ++ [x₁, x₂, x₃] = (xs ++ [x₁, x₂]) ++ [x₃] by simp]
    exact CausalApply.functionEvaluator_raw_append H
      (xs ++ [x₁, x₂]) x₃
  apply PFunConverter.DDC.apply_ofStep_functionEvaluator_of_round
      (sequenceHashStep b) H
      (fun q : Query => sequenceHash b H q.1 q.2)
      calls B (Bmax := 3)
  · intro q
    dsimp only [B]
    split <;> omega
  · intro q n xs
    rcases q with ⟨S, M⟩
    by_cases hS : S.val.length ≤ b.val
    · simp [B, calls, sequenceHashStep, hS, sequenceHash, derive,
        CausalApply.driveG,
        CausalApply.functionEvaluator_raw_append, hrawTwo]
    · simp [B, calls, sequenceHashStep, hS, sequenceHash, derive,
        CausalApply.driveG,
        CausalApply.functionEvaluator_raw_append, hrawTwo, hrawThree]

end RandomSystemsModel

end SequenceHash
