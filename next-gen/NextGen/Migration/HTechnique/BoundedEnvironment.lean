/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.BoundedEnvironment

/-!
# Bounded environments on the CR18 surface

This module keeps compatibility names for the exact bounded-environment bridge,
now promoted to the shared `RandomSystems.CR18` surface.

Source status:

* source-theorem bridge: the promoted `RandomSystems.CR18.boundedEnvironment`
  embeds a q-round total environment into a CR18 partial-function DDE by
  answering exactly concrete output histories of length `< q` and stopping
  otherwise.  There is no default query for histories containing `⊥` or for
  histories past the budget.

Migration note: this module is compatibility-only and can be removed after
downstream migration files use the shared names directly.
-/

noncomputable section

namespace NextGen
namespace Migration
namespace HTechnique

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- Compatibility alias for `RandomSystems.CR18.concreteOutputHistory`. -/
abbrev concreteOutputHistory : List (Option Y) → Option (List Y) :=
  RandomSystems.CR18.concreteOutputHistory

@[simp]
theorem concreteOutputHistory_map_some (ys : List Y) :
    concreteOutputHistory (ys.map some) = some ys := by
  exact RandomSystems.CR18.concreteOutputHistory_map_some ys

/-- Compatibility alias for `RandomSystems.CR18.boundedDDE`. -/
abbrev boundedDDE
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    RandomSystems.CR18.PFunDDS.DDE X Y :=
  RandomSystems.CR18.boundedDDE choose

/- The bounded environment answers concrete histories before the query budget
with exactly the bounded chooser's next query. -/
@[simp]
theorem boundedDDE_apply_map_some_of_lt
    (choose : (i : Fin q) → (Fin i.1 → Y) → X)
    (ys : List Y) (hlen : ys.length < q) :
    boundedDDE choose (ys.map some) =
      some (choose ⟨ys.length, hlen⟩ (fun j => ys.get j)) := by
  exact RandomSystems.CR18.boundedDDE_apply_map_some_of_lt choose ys hlen

/- Compatibility theorem for the promoted bounded-DDE length-indexed rewrite. -/
theorem boundedDDE_apply_map_some_of_length_eq
    (choose : (i : Fin q) → (Fin i.1 → Y) → X)
    (ys : List Y) (i : Fin q) (hlen_eq : ys.length = i.1) :
    boundedDDE choose (ys.map some) =
      some (choose i (fun j => ys.get ⟨j.1, by rw [hlen_eq]; exact j.2⟩)) := by
  exact RandomSystems.CR18.boundedDDE_apply_map_some_of_length_eq choose ys i hlen_eq

/-- Compatibility alias for `RandomSystems.CR18.boundedEnvironment`. -/
abbrev boundedEnvironment
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    RandomSystems.CR18.PFunPDE.RV PUnit X Y :=
  RandomSystems.CR18.boundedEnvironment choose

/- Compatibility theorem for the promoted q-query-totality theorem. -/
theorem boundedEnvironment_KQueryTotal
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    RandomSystems.CR18.PFunPDE.RV.KQueryTotal
      (boundedEnvironment choose) q := by
  exact RandomSystems.CR18.boundedEnvironment_KQueryTotal choose

/- Compatibility theorem for the promoted nonempty-environment witness. -/
theorem boundedEnvironment_subtype_nonempty
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    Nonempty
      {E : RandomSystems.CR18.PFunPDE.RV PUnit X Y //
        RandomSystems.CR18.PFunPDE.RV.KQueryTotal E q} :=
  RandomSystems.CR18.boundedEnvironment_subtype_nonempty choose

end HTechnique
end Migration
end NextGen
