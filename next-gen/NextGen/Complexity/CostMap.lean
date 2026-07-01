/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.Cost

/-!
# Cost maps

Cost maps are plain functions between cost domains.  This file collects the
small maps and monotonicity lemmas needed by costed reductions.
-/

namespace RandomSystems.CR18
namespace Complexity
namespace CostMap

variable {Label Label' Label'' : Type*}

/-- The identity cost map. -/
def id : Cost Label → Cost Label := _root_.id

@[simp] theorem id_apply (c : Cost Label) : id c = c := rfl

theorem monotone_id : Monotone (id : Cost Label → Cost Label) :=
  fun _ _ h => h

/-- Composition of cost maps. -/
def comp (g : Cost Label' → Cost Label'') (f : Cost Label → Cost Label') :
    Cost Label → Cost Label'' :=
  g ∘ f

@[simp] theorem comp_apply (g : Cost Label' → Cost Label'')
    (f : Cost Label → Cost Label') (c : Cost Label) :
    comp g f c = g (f c) := rfl

theorem monotone_comp {g : Cost Label' → Cost Label''} {f : Cost Label → Cost Label'}
    (hg : Monotone g) (hf : Monotone f) :
    Monotone (comp g f) :=
  hg.comp hf

/-- Add a fixed cost vector as overhead. -/
def addFixed (overhead : Cost Label) : Cost Label → Cost Label :=
  fun c => overhead + c

@[simp] theorem addFixed_apply (overhead c : Cost Label) :
    addFixed overhead c = overhead + c := rfl

theorem monotone_addFixed (overhead : Cost Label) :
    Monotone (addFixed overhead) := by
  intro a b h coord
  exact Nat.add_le_add_left (h coord) (overhead coord)

/-- Add fixed intrinsic work and leave call counts unchanged. -/
def addIntrinsic (n : Nat) : Cost Label → Cost Label :=
  fun c => Cost.of (n + Cost.intrinsic c) (Cost.calls c)

@[simp] theorem intrinsic_addIntrinsic (n : Nat) (c : Cost Label) :
    Cost.intrinsic (addIntrinsic n c) = n + Cost.intrinsic c := rfl

@[simp] theorem calls_addIntrinsic (n : Nat) (c : Cost Label) (l : Label) :
    Cost.calls (addIntrinsic n c) l = Cost.calls c l := rfl

theorem monotone_addIntrinsic (n : Nat) :
    Monotone (addIntrinsic (Label := Label) n) := by
  intro a b h
  rw [Cost.le_iff] at h ⊢
  exact ⟨Nat.add_le_add_left h.1 n, h.2⟩

/-- Relabel call coordinates, preserving intrinsic work. -/
def relabel (f : Label' → Label) : Cost Label → Cost Label' :=
  Cost.relabel f

@[simp] theorem relabel_apply (f : Label' → Label) (c : Cost Label) :
    relabel f c = Cost.relabel f c := rfl

theorem monotone_relabel (f : Label' → Label) :
    Monotone (relabel f : Cost Label → Cost Label') := by
  intro a b h
  rw [Cost.le_iff] at h ⊢
  exact ⟨h.1, fun l => h.2 (f l)⟩

end CostMap
end Complexity
end RandomSystems.CR18
