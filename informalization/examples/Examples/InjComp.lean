/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization

/-! Real end-to-end example (DESIGN §4(A)): a genuine core-Lean theorem,
informalized from its kernel-checked type and proof term. -/

open Informalization

/-- Composition of injective functions is injective. -/
theorem inj_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  fun a b h => hf (hg h)

-- Prints the informalized document as JSON (paste into web/index.html).
#informalize inj_comp
