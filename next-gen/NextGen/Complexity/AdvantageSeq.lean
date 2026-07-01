/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.GameBased
import NextGen.Complexity.GameSeq

/-!
# Distinguishing-advantage traces

This file specializes the generic `GameTrace` tooling to CR18/PFun
distinguishing systems.  The public endpoint bounds are phrased as named
statements over a trace; solver-level probability-distribution hypotheses stay
inside the proof of the supremum bound.
-/

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- A concrete PFun system trace for game-hopping arguments. -/
abbrev SystemTrace (X : Type u) (Y : Type v) : Type (max u v) :=
  GameTrace (PFunPDS X Y)

/-- The finite sum of adjacent maximal advantages along a system trace. -/
noncomputable def adjacentMaxAdvantageSum (systems : SystemTrace X Y) (n : Nat) : ℝ :=
  ∑ i ∈ Finset.range n, Δ(systems i, systems (i + 1))

/-- Statement form of the per-distinguisher telescoping identity. -/
abbrev DistinguisherAdvantageTelescope
    (D : DistinguisherSolver X Y) (systems : SystemTrace X Y) (n : Nat) : Prop :=
  advantage D (systems 0) (systems n) =
    ∑ i ∈ Finset.range n, advantage D (systems i) (systems (i + 1))

/-- Statement form for an endpoint maximal-advantage bound. -/
abbrev MaxAdvantageTraceBound (systems : SystemTrace X Y) (n : Nat) (bound : ℝ) : Prop :=
  Δ(systems 0, systems n) ≤ bound

/-- Statement form for pointwise adjacent maximal-advantage bounds. -/
abbrev AdjacentMaxAdvantageBounded
    (systems : SystemTrace X Y) (n : Nat) (stepBound : Nat → ℝ) : Prop :=
  ∀ i, i < n → Δ(systems i, systems (i + 1)) ≤ stepBound i

/-- CR18 hybrid telescoping for a fixed distinguisher. -/
theorem advantage_telescope
    (D : DistinguisherSolver X Y) (systems : SystemTrace X Y) (n : Nat) :
    DistinguisherAdvantageTelescope D systems n := by
  simp only [DistinguisherAdvantageTelescope, advantage]
  exact (Finset.sum_range_sub (fun i => (verdictProb D (systems i) : ℝ)) n).symm

/-- The endpoint maximal advantage is bounded by the sum of adjacent maximal
advantages. -/
theorem maxAdvantage_le_adjacent_sum (systems : SystemTrace X Y) (n : Nat) :
    MaxAdvantageTraceBound systems n (adjacentMaxAdvantageSum systems n) := by
  unfold MaxAdvantageTraceBound maxAdvantage adjacentMaxAdvantageSum
  refine csSup_le ?_ ?_
  · exact RandomSystems.CR18.advantage_image_nonempty (systems 0) (systems n)
  rintro x ⟨D, hD, rfl⟩
  change advantage D (systems 0) (systems n) ≤
    ∑ i ∈ Finset.range n, Δ(systems i, systems (i + 1))
  rw [advantage_telescope]
  exact Finset.sum_le_sum fun i _ =>
    advantage_le_maxAdvantage D (systems i) (systems (i + 1)) hD

namespace AdjacentMaxAdvantageBounded

variable {systems : SystemTrace X Y} {n : Nat} {stepBound : Nat → ℝ}

/-- Local adjacent bounds compose into one endpoint trace bound. -/
theorem traceBound (h : AdjacentMaxAdvantageBounded systems n stepBound) :
    MaxAdvantageTraceBound systems n (∑ i ∈ Finset.range n, stepBound i) := by
  exact le_trans (maxAdvantage_le_adjacent_sum systems n)
    (Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi))

end AdjacentMaxAdvantageBounded

/-- Three-hop hybrid bound.  This is the common proof shape in small
game-based reductions: prove the three local `Δ` bounds and let the trace
telescope do the global accounting. -/
theorem maxAdvantage_three_hop_le (systems : SystemTrace X Y) {b0 b1 b2 : ℝ}
    (h0 : Δ(systems 0, systems 1) ≤ b0)
    (h1 : Δ(systems 1, systems 2) ≤ b1)
    (h2 : Δ(systems 2, systems 3) ≤ b2) :
    Δ(systems 0, systems 3) ≤ b0 + b1 + b2 := by
  let localBound : Nat → ℝ
    | 0 => b0
    | 1 => b1
    | _ => b2
  have hsteps : AdjacentMaxAdvantageBounded systems 3 localBound := by
    intro i hi
    interval_cases i
    · simpa [localBound] using h0
    · simpa [localBound] using h1
    · simpa [localBound] using h2
  have htrace : MaxAdvantageTraceBound systems 3
      (∑ i ∈ Finset.range 3, localBound i) :=
    AdjacentMaxAdvantageBounded.traceBound hsteps
  have hsum : (∑ i ∈ Finset.range 3, localBound i) = b0 + b1 + b2 := by
    norm_num [Finset.sum_range_succ, localBound]
  exact le_trans htrace (le_of_eq hsum)

namespace AdjacentMaxAdvantageBounded

variable {systems : SystemTrace X Y} {stepBound : Nat → ℝ}

/-- Specialized three-hop trace bound from an adjacent-bound statement. -/
theorem threeHopBound (h : AdjacentMaxAdvantageBounded systems 3 stepBound) :
    Δ(systems 0, systems 3) ≤ stepBound 0 + stepBound 1 + stepBound 2 :=
  maxAdvantage_three_hop_le systems
    (h 0 (by norm_num)) (h 1 (by norm_num)) (h 2 (by norm_num))

end AdjacentMaxAdvantageBounded

end

end Complexity
end RandomSystems.CR18
