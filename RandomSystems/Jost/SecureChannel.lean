/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Surface
import RandomSystems.Jost.Construction

/-!
# Jost §2.2.6 on the authoring surface: the construction as behavioral identity

Prop. 2.2.17, restated where it belongs: on **resources** (the behavioral
quotient), in surface vocabulary.  `real`, `ideal`, and the two reduction
worlds `game b` are `Resource`s over the constructed interface declaration;
the two leaves of the thesis proof become *resource equalities*, obtained
from the machine-level bisimulations of `Jost/Construction.lean` through
`Resource.sampleInit_congr` (the identity coupling of the uniform seed).

The seed-indexed machine families are those of `Jost/Systems.lean`.  How
each fibre machine was assembled (the machine-level combinators of
`Jost/Combinators.lean`) is authoring detail of the family — a family is
just a function into realizations — and carries no proof obligation here:
the surface claim quantifies over the denoted behaviors only.

Because the leaves are equalities of resources, Prop. 2.2.17 needs no
metric: every functional Φ of the (real, ideal) pair takes the same value
on `(c CPA₀, c CPA₁)` — instantiating Φ with any distinguisher's advantage
is the thesis's `ε(D) := Δ^{Dc}(CPA₀, CPA₁)` transport, with zero slack,
now stated at the behavioral quotient. -/

namespace RandomSystems.CC.SecureChannel

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.TypedResource.JostFigure22 (Iface chanIn)
open RandomSystems.CR18.TypedResource.Jost226 (EncScheme Seed conOut
  realMachine idealMachine gameMachine
  realMachine_toDDS_eq_gameMachine idealMachine_toDDS_eq_gameMachine)

/-- The constructed boundary of Fig. 2.1, as an interface declaration:
Alice sends plaintexts, Bob receives, Eve leaks ciphertexts and delivers,
F delivers. -/
def constructedInterfaces (M C : Type) : Interfaces where
  Iface := Iface
  In := chanIn M
  Out := conOut M C

variable {K R M C L : Type} [Inhabited R] [DecidableEq L]
variable [Fintype K] [Nonempty K] [Fintype R]

/-- `π_E [AuthChan, Key]` as a resource: the real world. -/
noncomputable def real (E : EncScheme K R M C L) (cap : ℕ) :
    Resource (constructedInterfaces M C) :=
  Resource.sampleInit (realMachine E (cap := cap))
    (Dist.uniform (Seed K R cap)) Dist.uniform_isProbDist

/-- `σ_E SecChan` as a resource: the ideal world. -/
noncomputable def ideal (E : EncScheme K R M C L) (cap : ℕ) :
    Resource (constructedInterfaces M C) :=
  Resource.sampleInit (idealMachine E (cap := cap))
    (Dist.uniform (Seed K R cap)) Dist.uniform_isProbDist

/-- `c CPA_b` as a resource: the reduction against either game world. -/
noncomputable def game (E : EncScheme K R M C L) (b : Bool) (cap : ℕ) :
    Resource (constructedInterfaces M C) :=
  Resource.sampleInit (gameMachine E b (cap := cap))
    (Dist.uniform (Seed K R cap)) Dist.uniform_isProbDist

/-- **Leaf 1 at the resource**: the real world IS the reduction against
`CPA₀` — behavioral identity, from the per-seed bisimulation through the
identity coupling of the uniform seed. -/
theorem real_eq_game (E : EncScheme K R M C L) (cap : ℕ) :
    real (M := M) (C := C) E cap = game E false cap :=
  Resource.sampleInit_congr Dist.uniform_isProbDist fun seed _ =>
    realMachine_toDDS_eq_gameMachine E seed

/-- **Leaf 2 at the resource**: the ideal world IS the reduction against
`CPA₁` (the simulator's key is the game's key). -/
theorem ideal_eq_game (E : EncScheme K R M C L) (cap : ℕ) :
    ideal (M := M) (C := C) E cap = game E true cap :=
  Resource.sampleInit_congr Dist.uniform_isProbDist fun seed _ =>
    idealMachine_toDDS_eq_gameMachine E seed

/-- **Prop. 2.2.17 at the behavioral quotient**: every functional of the
(real, ideal) pair equals its value on the two reduction worlds — the
`ε(D) := Δ^{Dc}(CPA₀, CPA₁)` transport with the distinguisher class left
abstract and no metric slack. -/
theorem construction {α : Sort*} (E : EncScheme K R M C L) (cap : ℕ)
    (Φ : Resource (constructedInterfaces M C) →
      Resource (constructedInterfaces M C) → α) :
    Φ (real E cap) (ideal E cap) = Φ (game E false cap) (game E true cap) := by
  rw [real_eq_game, ideal_eq_game]

end RandomSystems.CC.SecureChannel
