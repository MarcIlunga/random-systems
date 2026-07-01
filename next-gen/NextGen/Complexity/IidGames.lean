/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.BitGuessing

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)

noncomputable section

universe u

def sampleSystem {A : Type u} (X : Dist A) : PFunPDS Unit A :=
  Dist.fTransform
    (fun x : A => PFunDDS.functionEvaluator (fun _ : Unit => x))
    X

def sampleGame {A : Type u} (X Y : Dist A) : BitGuessGame Unit A
  | false => sampleSystem X
  | true => sampleSystem Y

@[reducible] def sampleProblem (A : Type u) :
    Problem (BitGuessGame Unit A) (BitGuessSolver Unit A) ℝ :=
  bitGuessProblem Unit A

theorem sampleGame_same_secure {A : Type u} (X : Dist A) :
    (sampleProblem A).perf (sampleGame X X) =
      fun _ : BitGuessSolver Unit A => 0 := by
  funext D
  simp [bitGuessAdvantage, sampleGame]

end

end Complexity
end RandomSystems.CR18
