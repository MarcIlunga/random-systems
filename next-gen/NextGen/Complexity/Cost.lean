/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Cost coordinates for CR18 complexity side conditions

This file keeps cost accounting in the same style as the CR18/CC core:
costs are functions over coordinates, not records with semantic content.

`Cost Label = Option Label -> Nat` has one distinguished coordinate:

* `none` is intrinsic/concrete work;
* `some l` is the number of calls to the labelled oracle/procedure `l`.

All algebra and order are inherited pointwise from the function type.
-/

namespace RandomSystems.CR18

/-- A cost vector with one intrinsic coordinate and one coordinate per call label.

This is deliberately an abbreviation for a function type.  The CR18 semantics keep
their objects as functions/partial functions; complexity support refines the solver
class by a cost predicate rather than introducing a new semantic object. -/
abbrev Cost (Label : Type*) : Type _ := Option Label → Nat

namespace Cost

variable {Label : Type*}

/-- The intrinsic/concrete-work coordinate. -/
def intrinsic (c : Cost Label) : Nat := c none

/-- The call-count coordinate for a labelled oracle/procedure. -/
def calls (c : Cost Label) (l : Label) : Nat := c (some l)

/-- Build a cost vector from its intrinsic coordinate and call-count function. -/
def of (intrinsic : Nat) (calls : Label → Nat) : Cost Label
  | none => intrinsic
  | some l => calls l

@[simp] theorem intrinsic_of (n : Nat) (f : Label → Nat) :
    intrinsic (of n f) = n := rfl

@[simp] theorem calls_of (n : Nat) (f : Label → Nat) (l : Label) :
    calls (of n f) l = f l := rfl

@[simp] theorem of_intrinsic_calls (c : Cost Label) :
    of (intrinsic c) (calls c) = c := by
  funext coord
  cases coord <;> rfl

/-- Relabel call coordinates, leaving intrinsic work unchanged. -/
def relabel {Label' : Type*} (f : Label' → Label) (c : Cost Label) : Cost Label' :=
  of (intrinsic c) (fun l => calls c (f l))

@[simp] theorem intrinsic_relabel {Label' : Type*} (f : Label' → Label) (c : Cost Label) :
    intrinsic (relabel f c) = intrinsic c := rfl

@[simp] theorem calls_relabel {Label' : Type*} (f : Label' → Label) (c : Cost Label)
    (l : Label') :
    calls (relabel f c) l = calls c (f l) := rfl

@[simp] theorem intrinsic_zero : intrinsic (0 : Cost Label) = 0 := rfl

@[simp] theorem calls_zero (l : Label) : calls (0 : Cost Label) l = 0 := rfl

@[simp] theorem intrinsic_add (a b : Cost Label) :
    intrinsic (a + b) = intrinsic a + intrinsic b := rfl

@[simp] theorem calls_add (a b : Cost Label) (l : Label) :
    calls (a + b) l = calls a l + calls b l := rfl

@[simp] theorem intrinsic_nsmul (n : Nat) (c : Cost Label) :
    intrinsic (n • c) = n * intrinsic c := rfl

@[simp] theorem calls_nsmul (n : Nat) (c : Cost Label) (l : Label) :
    calls (n • c) l = n * calls c l := rfl

theorem le_iff (a b : Cost Label) :
    a ≤ b ↔ intrinsic a ≤ intrinsic b ∧ ∀ l, calls a l ≤ calls b l := by
  constructor
  · intro h
    exact ⟨h none, fun l => h (some l)⟩
  · intro h coord
    cases coord with
    | none => exact h.1
    | some l => exact h.2 l

theorem intrinsic_le_of_le {a b : Cost Label} (h : a ≤ b) :
    intrinsic a ≤ intrinsic b :=
  (le_iff a b).mp h |>.1

theorem calls_le_of_le {a b : Cost Label} (h : a ≤ b) (l : Label) :
    calls a l ≤ calls b l :=
  (le_iff a b).mp h |>.2 l

end Cost

end RandomSystems.CR18
