import SequenceHash.RandomSystems.DeferredSampling
import SequenceHash.RandomSystems.SequenceHashJoinBound

/-!
# Adaptive compression-graph join bound

This module closes the deferred-sampling step in the SequenceHash join
argument.  The compression points may be chosen adaptively from all earlier
answers.  If absence of a graph join makes those points distinct, the exact
restricted-law identity replaces their answers by independent uniform
coordinates.  The static three-witness count then applies unchanged.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems

universe u v

variable {Q : Type u} {C : Type v}

/-- Adaptive form of the IV/live/live/loose-root join count.  The hypothesis
`noJoinFresh` is the graph-specific obligation: it states that every repeated
adaptive primitive point already has one of the named `StaticJoin` witnesses. -/
theorem adaptiveRun_staticJoin_mass_le_budget
    [Fintype Q] [DecidableEq Q]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (schedule : AdaptiveSchedule Q C)
    (iv : C) (roots : Finset C) (s q : ℕ)
    (rootBudget : roots.card ≤ q)
    (noJoinFresh : ∀ values,
      ¬ StaticJoin iv roots s values → FreshAt schedule values) :
    (Dist.fTransform (fun oracle => adaptiveRun schedule oracle s)
      (Dist.uniform (Q → C))).mass (StaticJoin iv roots s) ≤
      ((Nat.choose (s + 1) 2 + q * s : ℕ) : ℝ) /
        (Fintype.card C : ℝ) := by
  classical
  let good : (Fin s → C) → Prop :=
    fun values => ¬ StaticJoin iv roots s values
  letI : DecidablePred good := Classical.decPred good
  have complementMass :=
    adaptiveRun_compl_mass_eq_uniform schedule s good
      (fun values isGood => noJoinFresh values isGood)
  change
    (Dist.fTransform (fun oracle => adaptiveRun schedule oracle s)
      (Dist.uniform (Q → C))).mass (StaticJoin iv roots s) ≤ _
  have eventEquality :
      (fun values => ¬ good values) = StaticJoin iv roots s := by
    funext values
    simp only [good, not_not]
  rw [← eventEquality, complementMass, eventEquality]
  exact uniform_staticJoin_mass_le_budget iv roots s q rootBudget

end MDSimulator
end RandomSystemsModel
end SequenceHash
