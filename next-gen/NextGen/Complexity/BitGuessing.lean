/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.GameBased
import NextGen.Complexity.GameHop

/-!
# Bit-guessing games

CR18 Def. 2.9 presents bit guessing as the experiment where a hidden bit selects
one of two systems and the solver outputs a bit.  For the PFun layer this is a
thin wrapper: a bit-guessing game is a `Bool`-indexed family of systems, and its
signed advantage is exactly the existing distinguishing advantage between the
`false` and `true` worlds.
-/

namespace RandomSystems.CR18
namespace Complexity

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- A bit-guessing game is a pair of systems indexed by the hidden bit. -/
abbrev BitGuessGame (X : Type u) (Y : Type v) : Type (max u v) :=
  Bool → PFunPDS X Y

/-- Bit-guessing solvers are the existing CR18 distinguishers, whose verdict
bit is read as the bit guess. -/
abbrev BitGuessSolver (X : Type u) (Y : Type v) : Type (max u v) :=
  DistinguisherSolver X Y

/-- View a bit-guessing game as the corresponding distinguishing pair. -/
def bitGuessAsDistinguishing (G : BitGuessGame X Y) : DistinguishingGame X Y :=
  (G false, G true)

/-- View a distinguishing pair as the corresponding bit-indexed game. -/
def distinguishingAsBitGuess (p : DistinguishingGame X Y) : BitGuessGame X Y
  | false => p.1
  | true => p.2

/-- CR18 bit-guessing advantage in signed form.  The `true` world contributes
positively and the `false` world negatively, so this is definitionally the
existing signed distinguishing advantage. -/
noncomputable def bitGuessAdvantage (D : BitGuessSolver X Y) (G : BitGuessGame X Y) : ℝ :=
  (verdictProb D (G true) : ℝ) - (verdictProb D (G false) : ℝ)

@[reducible] def bitGuessProblem (X : Type u) (Y : Type v) :
    Problem (BitGuessGame X Y) (BitGuessSolver X Y) ℝ where
  perf := fun G D => bitGuessAdvantage D G

@[simp] theorem bitGuessProblem_perf
    (G : BitGuessGame X Y) (D : BitGuessSolver X Y) :
    (bitGuessProblem X Y).perf G D = bitGuessAdvantage D G :=
  rfl

theorem bitGuessAdvantage_eq_advantage
    (G : BitGuessGame X Y) (D : BitGuessSolver X Y) :
    bitGuessAdvantage D G = advantage D (G false) (G true) := by
  rfl

theorem bitGuessAsDistinguishing_perf
    (G : BitGuessGame X Y) (D : BitGuessSolver X Y) :
    (distinguishingProblem X Y).perf (bitGuessAsDistinguishing G) D
      = (bitGuessProblem X Y).perf G D := by
  rfl

theorem distinguishingAsBitGuess_perf
    (p : DistinguishingGame X Y) (D : DistinguisherSolver X Y) :
    (bitGuessProblem X Y).perf (distinguishingAsBitGuess p) D
      = (distinguishingProblem X Y).perf p D := by
  rfl

@[simp] theorem bitGuessAsDistinguishing_distinguishingAsBitGuess
    (p : DistinguishingGame X Y) :
    bitGuessAsDistinguishing (distinguishingAsBitGuess p) = p := by
  rfl

@[simp] theorem distinguishingAsBitGuess_bitGuessAsDistinguishing
    (G : BitGuessGame X Y) :
    distinguishingAsBitGuess (bitGuessAsDistinguishing G) = G := by
  funext b
  cases b <;> rfl

/-- Exact-cost identity reduction from bit guessing to distinguishing. -/
abbrev BitGuessToDistinguishingReduction {Label : Type*}
    (G : BitGuessGame X Y) (gamma : BitGuessSolver X Y → Cost Label) : Prop :=
  @IsCostedReduction
    (BitGuessGame X Y) (BitGuessSolver X Y) ℝ
    (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ
    _ (bitGuessProblem X Y) _ (distinguishingProblem X Y)
    Label Label
    G (bitGuessAsDistinguishing G)
    (_root_.id : ℝ → ℝ)
    (_root_.id : BitGuessSolver X Y → DistinguisherSolver X Y)
    gamma gamma (CostMap.id : Cost Label → Cost Label)

/-- Exact-cost identity reduction from distinguishing to bit guessing. -/
abbrev DistinguishingToBitGuessReduction {Label : Type*}
    (p : DistinguishingGame X Y) (gamma : DistinguisherSolver X Y → Cost Label) : Prop :=
  @IsCostedReduction
    (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ
    (BitGuessGame X Y) (BitGuessSolver X Y) ℝ
    _ (distinguishingProblem X Y) _ (bitGuessProblem X Y)
    Label Label
    p (distinguishingAsBitGuess p)
    (_root_.id : ℝ → ℝ)
    (_root_.id : DistinguisherSolver X Y → BitGuessSolver X Y)
    gamma gamma (CostMap.id : Cost Label → Cost Label)

section Reductions

variable {Label : Type*}
variable {G : BitGuessGame X Y} {p : DistinguishingGame X Y}
variable {gamma : DistinguisherSolver X Y → Cost Label}

theorem bitGuess_toDistinguishing_isCostedReduction :
    BitGuessToDistinguishingReduction G gamma := by
  constructor
  · intro D
    simpa [BitGuessToDistinguishingReduction] using
      le_of_eq (bitGuessAsDistinguishing_perf G D).symm
  · intro D
    rfl

theorem distinguishing_toBitGuess_isCostedReduction :
    DistinguishingToBitGuessReduction p gamma := by
  constructor
  · intro D
    simpa [DistinguishingToBitGuessReduction] using
      le_of_eq (distinguishingAsBitGuess_perf p D).symm
  · intro D
    rfl

end Reductions

end

end Complexity
end RandomSystems.CR18
