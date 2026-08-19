/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.PRG
import RandomSystems.Complexity.SwitchingBridge
import RandomSystems.FunctionEvaluator

/-!
# Boneh-Shoup chapter 4: PRF and PRP games

Attack Game 4.2 is a distinguishing game between a keyed function family and a
uniform random function.  Attack Game 4.3 is the same interface specialized to
random permutations versus random functions; the bound is exactly CR18's
filtered URF/URP switching theorem.  The PRF-to-PRG endpoint below is
Boneh-Shoup Theorem 4.8's fixed-distinct-query construction at the level of
the two games.
-/

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)
open scoped RandomSystems.CR18

noncomputable section

universe u v w

namespace PRF

variable {Key : Type u} {X : Type v} {Y : Type w}

/-- Boneh-Shoup Attack Game 4.2, Experiment 0: sample a key and answer with
the keyed function `F k`. -/
def real (F : Key → X → Y) (keyDist : Dist Key) : PFunPDS X Y :=
  Dist.fTransform (fun k : Key => eval[F k]) keyDist

/-- Boneh-Shoup Attack Game 4.2, Experiment 1: answer with a uniform random
function. -/
def random (X : Type v) (Y : Type w) [Fintype (X → Y)] [Nonempty (X → Y)] :
    PFunPDS X Y :=
  PFunPDS.URF (X := X) (Y := Y)

/-- The two-experiment PRF distinguishing game. -/
def distinguishing (q : Nat) (F : Key → X → Y) (keyDist : Dist Key)
    [Fintype (X → Y)] [Nonempty (X → Y)] :
    DistinguishingGame X Y :=
  (⌈q⌉ (real F keyDist), ⌈q⌉ (random X Y))

/-- The bit-guessing recast of Attack Game 4.2. -/
def bitGuessGame (q : Nat) (F : Key → X → Y) (keyDist : Dist Key)
    [Fintype (X → Y)] [Nonempty (X → Y)] :
    BitGuessGame X Y :=
  distinguishingAsBitGuess (distinguishing q F keyDist)

/-- The CR18 signed maximal PRF advantage. -/
abbrev Advantage (q : Nat) (F : Key → X → Y) (keyDist : Dist Key)
    [Fintype (X → Y)] [Nonempty (X → Y)] : ℝ :=
  Δ((distinguishing q F keyDist).1, (distinguishing q F keyDist).2)

end PRF

namespace PRFToPRG

variable {Key : Type u} {X : Type v} {Y : Type w}
variable {LabelSample LabelPRF : Type*}

/-- Boneh-Shoup Theorem 4.8's derived generator:
`G(k) = (F(k,x₀), ..., F(k,x_{q-1}))`. -/
def derived {q : Nat} (F : Key → X → Y) (xs : Fin q → X) : Key → (Fin q → Y) :=
  fun k i => F k (xs i)

/-- The fixed-query construction needs at least one query and pairwise distinct
fixed inputs. -/
abbrev Hyp {q : Nat} (xs : Fin q → X) : Prop :=
  0 < q ∧ Function.Injective xs

/-- The PRG game for the derived generator is exactly the fixed-query
conversion of the `q`-query PRF game. -/
abbrev Goal {q : Nat} (F : Key → X → Y) (keyDist : Dist Key)
    (xs : Fin q → X) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] : Prop :=
  PRG.distinguishing (derived F xs) keyDist (Dist.uniform (Fin q → Y)) =
    convertDistinguishingGame (fixedQueryApplyPDS xs) (PRF.distinguishing q F keyDist)

/-- Boneh-Shoup Theorem 4.8's game endpoint: the constructed PRG worlds are the
fixed-query conversion of the corresponding PRF worlds. -/
theorem endpoints
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : Nat} {F : Key → X → Y} {keyDist : Dist Key} {xs : Fin q → X}
    (h : Hyp xs) :
    Goal F keyDist xs := by
  obtain ⟨hq, hxs⟩ := h
  apply Prod.ext
  · change PRG.real (derived F xs) keyDist =
      fixedQueryApplyPDS xs (PFunPDS.filterQueries q (PRF.real F keyDist))
    unfold PRG.real PRF.real
    rw [show Dist.fTransform (fun k : Key => eval[F k]) keyDist =
        PFunPDS.ofFunDist (Dist.fTransform F keyDist) by
      unfold PFunPDS.ofFunDist
      rw [Dist.fTransform_comp]
      rfl]
    rw [fixedQueryApplyPDS_filterQueries_ofFunDist xs (Dist.fTransform F keyDist) hq]
    rw [Dist.fTransform_comp]
    rfl
  · change PRG.random (Dist.uniform (Fin q → Y)) =
      fixedQueryApplyPDS xs (PFunPDS.filterQueries q (PRF.random X Y))
    unfold PRG.random PRF.random PFunPDS.URF
    rw [fixedQueryApplyPDS_filterQueries_ofFunDist xs (Dist.uniform (X → Y)) hq]
    rw [uniformFunction_eval_uniform xs hxs]

/-- PRF adversary induced by a PRG sample adversary and fixed inputs. -/
def reduceAdversary {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) : PFunDDS.DDD X Y :=
  fixedQuerySampleDDD xs Aadv

/-- Point-mass PRG distinguisher for a one-sample adversary. -/
noncomputable def sampleDistinguisher {q : Nat}
    (Aadv : SampleSolver (Fin q → Y)) : DistinguisherSolver Unit (Fin q → Y) :=
  pointDistinguisher (sampleDDD Aadv)

/-- Point-mass PRF distinguisher obtained by the fixed-query reduction. -/
noncomputable def reducedDistinguisher {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) : DistinguisherSolver X Y :=
  pointDistinguisher (reduceAdversary xs Aadv)

/-- Per-adversary PRF-to-PRG reduction statement: every PRG sample adversary
has exactly the same signed advantage as the fixed-query PRF adversary. -/
abbrev ReductionGoal {q : Nat} (F : Key → X → Y) (keyDist : Dist Key)
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y))
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] : Prop :=
  advantage (sampleDistinguisher Aadv)
      (PRG.real (derived F xs) keyDist) (PRG.random (Dist.uniform (Fin q → Y))) =
    advantage (reducedDistinguisher xs Aadv)
      (PRF.distinguishing q F keyDist).1 (PRF.distinguishing q F keyDist).2

/-- Boneh-Shoup Theorem 4.8's concrete adversary reduction. -/
theorem reduction
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : Nat} {F : Key → X → Y} {keyDist : Dist Key} {xs : Fin q → X}
    {Aadv : SampleSolver (Fin q → Y)}
    (hxs : Function.Injective xs) :
    ReductionGoal F keyDist xs Aadv := by
  classical
  have hReal :
      verdictProb (sampleDistinguisher Aadv) (PRG.real (derived F xs) keyDist) =
        verdictProb (reducedDistinguisher xs Aadv) (PRF.distinguishing q F keyDist).1 := by
    unfold sampleDistinguisher reducedDistinguisher reduceAdversary PRG.real
      PRF.distinguishing PRF.real
    rw [verdictProb_sampleDDD_sampleSystem]
    rw [show Dist.fTransform (fun k : Key => eval[F k]) keyDist =
        PFunPDS.ofFunDist (Dist.fTransform F keyDist) by
      unfold PFunPDS.ofFunDist
      rw [Dist.fTransform_comp]
      rfl]
    rw [verdictProb_fixedQuerySampleDDD_filterQueries_ofFunDist]
    rw [Dist.mass_fTransform, Dist.mass_fTransform]
    rfl
  have hRandom :
      verdictProb (sampleDistinguisher Aadv) (PRG.random (Dist.uniform (Fin q → Y))) =
        verdictProb (reducedDistinguisher xs Aadv) (PRF.distinguishing q F keyDist).2 := by
    unfold sampleDistinguisher reducedDistinguisher reduceAdversary PRG.random
      PRF.distinguishing PRF.random PFunPDS.URF
    rw [verdictProb_sampleDDD_sampleSystem]
    rw [verdictProb_fixedQuerySampleDDD_filterQueries_ofFunDist]
    rw [← uniformFunction_eval_uniform xs hxs]
    rw [Dist.mass_fTransform]
  unfold ReductionGoal advantage
  rw [hReal, hRandom]

/-- Problem dictionary for Boneh-Shoup one-sample distinguishers against a
distinguishing pair. -/
@[reducible] noncomputable def sampleDistinguishingProblem {q : Nat} :
    Problem (DistinguishingGame Unit (Fin q → Y)) (SampleSolver (Fin q → Y)) ℝ where
  perf := fun p Aadv => advantage (sampleDistinguisher Aadv) p.1 p.2

/-- Cost-side law for the concrete PRF-to-PRG adversary map. -/
abbrev ReductionCostBound {q : Nat}
    (xs : Fin q → X)
    (gammaSample : SampleSolver (Fin q → Y) → Cost LabelSample)
    (gammaPRF : DistinguisherSolver X Y → Cost LabelPRF)
    (costMap : Cost LabelSample → Cost LabelPRF) : Prop :=
  ∀ Aadv, gammaPRF (reducedDistinguisher xs Aadv) ≤ costMap (gammaSample Aadv)

/-- Named hypothesis for the concrete costed PRF-to-PRG reduction. -/
abbrev ReductionHyp {q : Nat}
    (xs : Fin q → X)
    (gammaSample : SampleSolver (Fin q → Y) → Cost LabelSample)
    (gammaPRF : DistinguisherSolver X Y → Cost LabelPRF)
    (costMap : Cost LabelSample → Cost LabelPRF) : Prop :=
  Function.Injective xs ∧ ReductionCostBound xs gammaSample gammaPRF costMap

/-- Costed-reduction statement for Boneh-Shoup Theorem 4.8. -/
abbrev CostedReduction {q : Nat} (F : Key → X → Y) (keyDist : Dist Key)
    (xs : Fin q → X)
    (gammaSample : SampleSolver (Fin q → Y) → Cost LabelSample)
    (gammaPRF : DistinguisherSolver X Y → Cost LabelPRF)
    (costMap : Cost LabelSample → Cost LabelPRF)
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] : Prop :=
  @IsCostedReduction
    (DistinguishingGame Unit (Fin q → Y)) (SampleSolver (Fin q → Y)) ℝ
    (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ
    _ sampleDistinguishingProblem _ (distinguishingProblem X Y)
    LabelSample LabelPRF
    (PRG.distinguishing (derived F xs) keyDist (Dist.uniform (Fin q → Y)))
    (PRF.distinguishing q F keyDist)
    (_root_.id : ℝ → ℝ)
    (reducedDistinguisher xs)
    gammaSample gammaPRF costMap

/-- The concrete adversary equality plus a concrete cost law gives the CR18
costed-reduction object. -/
theorem costedReduction
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : Nat} {F : Key → X → Y} {keyDist : Dist Key} {xs : Fin q → X}
    {gammaSample : SampleSolver (Fin q → Y) → Cost LabelSample}
    {gammaPRF : DistinguisherSolver X Y → Cost LabelPRF}
    {costMap : Cost LabelSample → Cost LabelPRF}
    (h : ReductionHyp xs gammaSample gammaPRF costMap) :
    CostedReduction F keyDist xs gammaSample gammaPRF costMap := by
  rcases h with ⟨hxs, hcost⟩
  constructor
  · intro Aadv
    simpa [CostedReduction, sampleDistinguishingProblem] using
      le_of_eq (reduction (F := F) (keyDist := keyDist) (xs := xs) (Aadv := Aadv) hxs)
  · exact hcost

end PRFToPRG

namespace PRP

variable {Key : Type u} {X : Type v}

/-- PRP/BC real world: sample a key and answer with the keyed permutation. -/
def real (E : Key → Equiv.Perm X) (keyDist : Dist Key) : PFunPDS X X :=
  Dist.fTransform (fun k : Key => eval[(E k).toFun]) keyDist

/-- Ideal PRP/BC world: answer with a uniform random permutation. -/
def random (X : Type v) [Fintype X] : PFunPDS X X :=
  PFunPDS.URP X

/-- The two-experiment PRP/block-cipher distinguishing game. -/
def distinguishing (q : Nat) (E : Key → Equiv.Perm X) (keyDist : Dist Key)
    [Fintype X] :
    DistinguishingGame X X :=
  (⌈q⌉ (real E keyDist), ⌈q⌉ (random X))

/-- The bit-guessing recast of the PRP/block-cipher game. -/
def bitGuessGame (q : Nat) (E : Key → Equiv.Perm X) (keyDist : Dist Key)
    [Fintype X] :
    BitGuessGame X X :=
  distinguishingAsBitGuess (distinguishing q E keyDist)

/-- The CR18 signed maximal PRP/block-cipher advantage. -/
abbrev Advantage (q : Nat) (E : Key → Equiv.Perm X) (keyDist : Dist Key)
    [Fintype X] : ℝ :=
  Δ((distinguishing q E keyDist).1, (distinguishing q E keyDist).2)

end PRP

namespace FunctionVsPermutation

/-- Boneh-Shoup Attack Game 4.3 in the CR18 orientation needed by the
switching theorem: uniform random function versus uniform random permutation. -/
def distinguishing (X : Type u) [Fintype X] [Nonempty X] (q : Nat) :
    DistinguishingGame X X :=
  letI := Classical.decEq X
  (⌈q⌉ (PRF.random X X), ⌈q⌉ (PRP.random X))

/-- Boneh-Shoup Theorem 4.6 / CR18 URF-URP switching bound. -/
abbrev Goal (X : Type u) [Fintype X] [Nonempty X] (q : Nat) : Prop :=
  Δ((distinguishing X q).1, (distinguishing X q).2)
    ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ)

theorem bound (X : Type u) [Fintype X] [Nonempty X] (q : Nat) :
    Goal X q := by
  simpa [Goal, distinguishing, PRF.random, PRP.random,
    URFURPSwitchingBound] using URFURPSwitchingBound.of_finite X q

end FunctionVsPermutation

end

end Complexity
end RandomSystems.CR18
