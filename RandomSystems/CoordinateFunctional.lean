import RandomSystems.HTechnique.Derivation
import RandomSystems.SwitchingLemma

/-!
# Finite unions of coordinate-functional events

A seed event costs one inverse-alphabet factor when, after fixing every other
coordinate, it pins the selected coordinate to at most one value.  This is the
right abstraction for adaptive graph arguments: the witness may be selected
from a complete transcript and may refer to a value sampled either before or
after its target, but it must still be functional in one genuinely hidden
uniform coordinate.
-/

noncomputable section

namespace RandomSystems

open RandomSystems.CR18

universe u v w

variable {I : Type u} {A : Type v} {W : Type w}

/-- A finite family of events, each with one coordinate in which it is
functional after all other coordinates have been fixed. -/
structure CoordinateFunctionalFamily
    (I : Type u) (A : Type v) (W : Type w) where
  coordinate : W → I
  event : W → (I → A) → Prop
  functional : ∀ witness left right,
    (∀ index, index ≠ coordinate witness → left index = right index) →
    event witness left → event witness right →
      left (coordinate witness) = right (coordinate witness)

/-- Union of all coordinate-functional witness events. -/
def CoordinateFunctionalFamily.Bad
    (family : CoordinateFunctionalFamily I A W) (seed : I → A) : Prop :=
  ∃ witness, family.event witness seed

instance CoordinateFunctionalFamily.instDecidableBad
    [Fintype W]
    (family : CoordinateFunctionalFamily I A W)
    [∀ witness, DecidablePred (family.event witness)] :
    DecidablePred family.Bad := by
  intro seed
  unfold CoordinateFunctionalFamily.Bad
  infer_instance

/-- Every member of a coordinate-functional family has uniform mass at most
`1 / |A|`. -/
theorem CoordinateFunctionalFamily.uniform_event_mass_le
    [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A]
    (family : CoordinateFunctionalFamily I A W) (witness : W) :
    (Dist.uniform (I → A)).mass (family.event witness) ≤
      1 / (Fintype.card A : ℝ) := by
  classical
  have bound := CR18.HTechniqueDerivation.uniform_pi_functional
    (family.coordinate witness) (family.event witness)
    (family.functional witness)
  simpa only [NNReal.coe_inv, NNReal.coe_natCast, one_div] using bound

/-- A union of `|W|` coordinate-functional events costs at most
`|W| / |A|`.  No chronological ordering of the witness and its target is
assumed. -/
theorem CoordinateFunctionalFamily.uniform_bad_mass_le
    [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A]
    [Fintype W]
    (family : CoordinateFunctionalFamily I A W) :
    (Dist.uniform (I → A)).mass family.Bad ≤
      (Fintype.card W : ℝ) / (Fintype.card A : ℝ) := by
  classical
  have cover :
      family.Bad =
        (fun seed => ∃ witness ∈ (Finset.univ : Finset W),
          family.event witness seed) := by
    funext seed
    simp [CoordinateFunctionalFamily.Bad]
  rw [cover]
  calc
    (Dist.uniform (I → A)).mass
          (fun seed => ∃ witness ∈ (Finset.univ : Finset W),
            family.event witness seed) ≤
        ∑ witness ∈ (Finset.univ : Finset W),
          (Dist.uniform (I → A)).mass (family.event witness) :=
      CR18.mass_biUnion_le _ Dist.uniform_nonNeg _ _
    _ ≤ ∑ _witness ∈ (Finset.univ : Finset W),
          1 / (Fintype.card A : ℝ) := by
      exact Finset.sum_le_sum fun witness _member =>
        family.uniform_event_mass_le witness
    _ = (Fintype.card W : ℝ) / (Fintype.card A : ℝ) := by
      simp [div_eq_mul_inv]

end RandomSystems
