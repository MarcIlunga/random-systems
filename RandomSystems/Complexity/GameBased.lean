/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.PFunProblems
import RandomSystems.Lemma415

/-!
# Game-based adapters

This file names the concrete PFun game-based surfaces in the complexity
namespace.  The underlying objects are still the existing PFun systems,
winners, and distinguishers.
-/

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)

universe u v

/-- A concrete PFun winning game. -/
abbrev WinningGame (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunGameProblem X Y

/-- A concrete PFun winner/adversary for a winning game. -/
abbrev WinnerSolver (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunGameSolver X Y

/-- A concrete PFun distinguishing problem. -/
abbrev DistinguishingGame (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunDistProblem X Y

/-- A concrete PFun distinguisher/adversary. -/
abbrev DistinguisherSolver (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunDistSolver X Y

/-- A one-sample adversary: receive one sample and return the verdict bit. -/
abbrev SampleSolver (A : Type u) : Type u :=
  A → Bool

/-- Query-bounded deterministic-system notation for game-based statements.
Use the existing probabilistic-system notation `⌈q⌉ S` for `PFunPDS` worlds. -/
scoped notation:max "⟦" q "⟧" S => PFunDDS.filterQueries q S

/-- Deterministic function oracle notation for game-based examples. -/
scoped notation:max "eval[" f "]" => PFunDDS.functionEvaluator f

/-- Verdict notation: the solver/adversary accepts the deterministic system. -/
scoped infix:50 " ⊨ " => PFunDDS.verdict

/-- A DDD that asks a `Unit` sample oracle once, then applies a one-sample
adversary to the reply. Missing replies are rejected. -/
def sampleDDDStep {A : Type u} (Aadv : SampleSolver A) :
    List (Option A) → Unit ⊕ Bool
  | [] => Sum.inl ()
  | some a :: _ => Sum.inr (Aadv a)
  | none :: _ => Sum.inr false

theorem sampleDDDStep_stopFinal {A : Type u} (Aadv : SampleSolver A) :
    PFunDDS.StopFinal (sampleDDDStep Aadv) := by
  intro h h' hprefix b hb
  obtain ⟨tail, rfl⟩ := hprefix
  cases h with
  | nil => simp [sampleDDDStep] at hb
  | cons a? _ => cases a? <;> simp [sampleDDDStep] at hb ⊢ <;> exact hb

/-- Embed a one-sample adversary as a one-query CR18 distinguisher. -/
def sampleDDD {A : Type u} (Aadv : SampleSolver A) : PFunDDS.DDD Unit A :=
  ⟨sampleDDDStep Aadv, sampleDDDStep_stopFinal Aadv⟩

theorem sampleDDD_queriesExactly {A : Type u} (Aadv : SampleSolver A) :
    QueriesExactly (PFunDDS.ddToDDE (sampleDDD Aadv)) 1 := by
  constructor
  · intro h hlen
    cases h with
    | nil => simp [PFunDDS.ddToDDE, sampleDDD, sampleDDDStep]
    | cons _ _ => simp at hlen
  · intro h hlen
    cases h with
    | nil => simp at hlen
    | cons a? _ => cases a? <;> simp [PFunDDS.ddToDDE, sampleDDD, sampleDDDStep]

/-- A reusable two-query equality distinguisher: ask `x₀`, then `x₁`, and
accept exactly when both replies are defined and equal. -/
def twoQueryEqStep {X : Type u} {Y : Type v} [DecidableEq Y] (x₀ x₁ : X) :
    List (Option Y) → X ⊕ Bool
  | [] => Sum.inl x₀
  | [_] => Sum.inl x₁
  | some y₀ :: some y₁ :: _ => Sum.inr (y₀ = y₁)
  | _ :: _ :: _ => Sum.inr false

/-- The deterministic two-query equality distinguisher. -/
def twoQueryEqDDS {X : Type u} {Y : Type v} [DecidableEq Y] (x₀ x₁ : X) :
    PFunDDS.DDD X Y :=
  ⟨twoQueryEqStep x₀ x₁, by
    intro h h' hprefix b hb
    rcases hprefix with ⟨tail, rfl⟩
    cases h with
    | nil =>
        simp [twoQueryEqStep] at hb
    | cons y₀ ys =>
        cases ys with
        | nil =>
            simp [twoQueryEqStep] at hb
        | cons y₁ ys =>
            cases y₀ <;> cases y₁ <;> simpa [twoQueryEqStep] using hb⟩

/-- Notation for the reusable two-query equality distinguisher. -/
scoped notation:max "A₂[" x₀ ", " x₁ "]" => twoQueryEqDDS x₀ x₁

theorem twoQueryEq_queriesExactly {X : Type u} {Y : Type v} [DecidableEq Y]
    (x₀ x₁ : X) :
    QueriesExactly (PFunDDS.ddToDDE (A₂[x₀, x₁] : PFunDDS.DDD X Y)) 2 := by
  constructor
  · intro h hlen
    cases h with
    | nil =>
        simp [PFunDDS.ddToDDE, twoQueryEqDDS, twoQueryEqStep]
    | cons y₀ ys =>
        cases ys with
        | nil =>
            simp [PFunDDS.ddToDDE, twoQueryEqDDS, twoQueryEqStep]
        | cons y₁ ys =>
            simp at hlen
  · intro h hlen
    cases h with
    | nil =>
        simp at hlen
    | cons y₀ ys =>
        cases ys with
        | nil =>
            simp at hlen
        | cons y₁ ys =>
            cases y₀ <;> cases y₁ <;>
              simp [PFunDDS.ddToDDE, twoQueryEqDDS, twoQueryEqStep]

theorem twoQueryEq_transcript_two_functionEvaluator
    {X : Type u} {Y : Type v} [DecidableEq Y] (x₀ x₁ : X) (f : X → Y) :
    PFunDDS.transcript (⟦2⟧ eval[f])
        (PFunDDS.ddToDDE (A₂[x₀, x₁] : PFunDDS.DDD X Y)) 2 =
      [(x₀, some (f x₀)), (x₁, some (f x₁))] := by
  simp [PFunDDS.transcript, PFunDDS.ddToDDE, twoQueryEqDDS,
    twoQueryEqStep, PFunDDS.output, PFunDDS.fullyDefined,
    PFunDDS.keptPrefix, PFunDDS.dom, PFunDDS.filterQueries,
    PFunDDS.functionEvaluator, PFunDDS.transcriptOutputs,
    PFunDDS.transcriptInputs]

/-- The CR18 problem dictionary for concrete PFun winning games. -/
@[reducible] noncomputable def winningProblem (X : Type u) (Y : Type v) :
    Problem (WinningGame X Y) (WinnerSolver X Y) ℝ :=
  pfunWinningProblem X Y

/-- The CR18 problem dictionary for concrete PFun distinguishing games. -/
@[reducible] noncomputable def distinguishingProblem (X : Type u) (Y : Type v) :
    Problem (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ :=
  pfunDistinguishingProblem X Y

@[simp] theorem winningProblem_perf
    {X : Type u} {Y : Type v} (G : WinningGame X Y) (W : WinnerSolver X Y) :
    (winningProblem X Y).perf G W = winProb W G :=
  rfl

@[simp] theorem distinguishingProblem_perf
    {X : Type u} {Y : Type v} (p : DistinguishingGame X Y)
    (D : DistinguisherSolver X Y) :
    (distinguishingProblem X Y).perf p D = advantage D p.1 p.2 :=
  rfl

end Complexity
end RandomSystems.CR18
