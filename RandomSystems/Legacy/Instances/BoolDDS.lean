/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.DDS

/-!
# Example: Boolean Single-Query Systems

Paper Example 4: The four (Bool, Bool)-DDS for q = 1 are:
  zero : x ↦ false
  one  : x ↦ true
  id   : x ↦ x
  flip : x ↦ ¬x

This file defines these systems and verifies basic properties.
-/

noncomputable section

namespace RandomSystems.Instances

/-- The constant-false DDS. -/
def zeroDDS : DDS Bool Bool 1 := DDS.ofFun (fun _ => false)

/-- The constant-true DDS. -/
def oneDDS : DDS Bool Bool 1 := DDS.ofFun (fun _ => true)

/-- The identity DDS. -/
def idDDS : DDS Bool Bool 1 := DDS.ofFun id

/-- The negation DDS. -/
def flipDDS : DDS Bool Bool 1 := DDS.ofFun Bool.not

/-- The four Boolean DDS are pairwise distinct. -/
theorem zeroDDS_ne_oneDDS : zeroDDS ≠ oneDDS := by
  intro h
  have := congr_fun (congr_fun (congr_arg DDS.respond h) ⟨0, Nat.zero_lt_one⟩)
    (fun _ => false)
  simp [zeroDDS, oneDDS, DDS.ofFun] at this

theorem zeroDDS_ne_idDDS : zeroDDS ≠ idDDS := by
  intro h
  have := congr_fun (congr_fun (congr_arg DDS.respond h) ⟨0, Nat.zero_lt_one⟩)
    (fun _ => true)
  simp [zeroDDS, idDDS, DDS.ofFun] at this

theorem idDDS_ne_flipDDS : idDDS ≠ flipDDS := by
  intro h
  have := congr_fun (congr_fun (congr_arg DDS.respond h) ⟨0, Nat.zero_lt_one⟩)
    (fun _ => true)
  simp [idDDS, flipDDS, DDS.ofFun] at this

end RandomSystems.Instances
